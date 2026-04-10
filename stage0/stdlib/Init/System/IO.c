// Lean compiler output
// Module: Init.System.IO
// Imports: public import Init.Control.Do public import Init.System.IOError public import Init.System.FilePath import Init.Data.String.TakeDrop import Init.Data.String.Search public import Init.Data.Ord.Basic public import Init.Data.String.Basic import Init.Data.List.MapIdx import Init.Data.Ord.UInt import Init.Data.ToString.Macro import Init.Data.List.Impl import Init.Data.Int.Repr
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
uint32_t lean_uint32_lor(uint32_t, uint32_t);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_byte_array_get(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
lean_object* l_MonadExcept_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_dbg_sleep(uint32_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_RealWorld_nonemptyType;
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadBaseIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadBaseIO___aux__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadBaseIO___closed__0 = (const lean_object*)&l_instMonadBaseIO___closed__0_value;
static const lean_closure_object l_instMonadBaseIO___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadBaseIO___aux__3___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadBaseIO___closed__1 = (const lean_object*)&l_instMonadBaseIO___closed__1_value;
static const lean_ctor_object l_instMonadBaseIO___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadBaseIO___closed__0_value),((lean_object*)&l_instMonadBaseIO___closed__1_value)}};
static const lean_object* l_instMonadBaseIO___closed__2 = (const lean_object*)&l_instMonadBaseIO___closed__2_value;
static const lean_closure_object l_instMonadBaseIO___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadBaseIO___aux__5___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadBaseIO___closed__3 = (const lean_object*)&l_instMonadBaseIO___closed__3_value;
static const lean_closure_object l_instMonadBaseIO___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadBaseIO___aux__7___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadBaseIO___closed__4 = (const lean_object*)&l_instMonadBaseIO___closed__4_value;
static const lean_closure_object l_instMonadBaseIO___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadBaseIO___aux__9___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadBaseIO___closed__5 = (const lean_object*)&l_instMonadBaseIO___closed__5_value;
static const lean_closure_object l_instMonadBaseIO___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadBaseIO___aux__11___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadBaseIO___closed__6 = (const lean_object*)&l_instMonadBaseIO___closed__6_value;
static const lean_ctor_object l_instMonadBaseIO___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadBaseIO___closed__2_value),((lean_object*)&l_instMonadBaseIO___closed__3_value),((lean_object*)&l_instMonadBaseIO___closed__4_value),((lean_object*)&l_instMonadBaseIO___closed__5_value),((lean_object*)&l_instMonadBaseIO___closed__6_value)}};
static const lean_object* l_instMonadBaseIO___closed__7 = (const lean_object*)&l_instMonadBaseIO___closed__7_value;
static const lean_closure_object l_instMonadBaseIO___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadBaseIO___aux__13___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadBaseIO___closed__8 = (const lean_object*)&l_instMonadBaseIO___closed__8_value;
static const lean_ctor_object l_instMonadBaseIO___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadBaseIO___closed__7_value),((lean_object*)&l_instMonadBaseIO___closed__8_value)}};
static const lean_object* l_instMonadBaseIO___closed__9 = (const lean_object*)&l_instMonadBaseIO___closed__9_value;
LEAN_EXPORT const lean_object* l_instMonadBaseIO = (const lean_object*)&l_instMonadBaseIO___closed__9_value;
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO___aux__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadFinallyBaseIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyBaseIO___aux__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadFinallyBaseIO___closed__0 = (const lean_object*)&l_instMonadFinallyBaseIO___closed__0_value;
LEAN_EXPORT const lean_object* l_instMonadFinallyBaseIO = (const lean_object*)&l_instMonadFinallyBaseIO___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadAttachBaseIO___aux__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachBaseIO___aux__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachBaseIO___aux__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachBaseIO___aux__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadAttachBaseIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadAttachBaseIO___aux__3___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadAttachBaseIO___closed__0 = (const lean_object*)&l_instMonadAttachBaseIO___closed__0_value;
LEAN_EXPORT const lean_object* l_instMonadAttachBaseIO = (const lean_object*)&l_instMonadAttachBaseIO___closed__0_value;
LEAN_EXPORT lean_object* l_BaseIO_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_map___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_map(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toEIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadLiftBaseIOEIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadLiftBaseIOEIO___closed__0 = (const lean_object*)&l_instMonadLiftBaseIOEIO___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_catchExceptions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadEIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___closed__0 = (const lean_object*)&l_instMonadEIO___closed__0_value;
static const lean_closure_object l_instMonadEIO___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__3___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___closed__1 = (const lean_object*)&l_instMonadEIO___closed__1_value;
static const lean_ctor_object l_instMonadEIO___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadEIO___closed__0_value),((lean_object*)&l_instMonadEIO___closed__1_value)}};
static const lean_object* l_instMonadEIO___closed__2 = (const lean_object*)&l_instMonadEIO___closed__2_value;
static const lean_closure_object l_instMonadEIO___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__5___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___closed__3 = (const lean_object*)&l_instMonadEIO___closed__3_value;
static const lean_closure_object l_instMonadEIO___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__7___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___closed__4 = (const lean_object*)&l_instMonadEIO___closed__4_value;
static const lean_closure_object l_instMonadEIO___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__9___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___closed__5 = (const lean_object*)&l_instMonadEIO___closed__5_value;
static const lean_closure_object l_instMonadEIO___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__11___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___closed__6 = (const lean_object*)&l_instMonadEIO___closed__6_value;
static const lean_ctor_object l_instMonadEIO___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadEIO___closed__2_value),((lean_object*)&l_instMonadEIO___closed__3_value),((lean_object*)&l_instMonadEIO___closed__4_value),((lean_object*)&l_instMonadEIO___closed__5_value),((lean_object*)&l_instMonadEIO___closed__6_value)}};
static const lean_object* l_instMonadEIO___closed__7 = (const lean_object*)&l_instMonadEIO___closed__7_value;
static const lean_closure_object l_instMonadEIO___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__13___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___closed__8 = (const lean_object*)&l_instMonadEIO___closed__8_value;
static const lean_ctor_object l_instMonadEIO___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadEIO___closed__7_value),((lean_object*)&l_instMonadEIO___closed__8_value)}};
static const lean_object* l_instMonadEIO___closed__9 = (const lean_object*)&l_instMonadEIO___closed__9_value;
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadFinallyEIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyEIO___aux__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadFinallyEIO___closed__0 = (const lean_object*)&l_instMonadFinallyEIO___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadAttachEIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadAttachEIO___aux__3___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadAttachEIO___closed__0 = (const lean_object*)&l_instMonadAttachEIO___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadAttachEIO(lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadExceptOfEIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadExceptOfEIO___aux__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadExceptOfEIO___closed__0 = (const lean_object*)&l_instMonadExceptOfEIO___closed__0_value;
static const lean_closure_object l_instMonadExceptOfEIO___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadExceptOfEIO___aux__3___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadExceptOfEIO___closed__1 = (const lean_object*)&l_instMonadExceptOfEIO___closed__1_value;
static const lean_ctor_object l_instMonadExceptOfEIO___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadExceptOfEIO___closed__0_value),((lean_object*)&l_instMonadExceptOfEIO___closed__1_value)}};
static const lean_object* l_instMonadExceptOfEIO___closed__2 = (const lean_object*)&l_instMonadExceptOfEIO___closed__2_value;
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object*);
static lean_once_cell_t l_instOrElseEIO___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instOrElseEIO___closed__0;
static lean_once_cell_t l_instOrElseEIO___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instOrElseEIO___closed__1;
static lean_once_cell_t l_instOrElseEIO___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instOrElseEIO___closed__2;
LEAN_EXPORT lean_object* l_instOrElseEIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_map___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_throw___redArg(lean_object*);
LEAN_EXPORT lean_object* l_EIO_throw___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_throw(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_throw___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_tryCatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg(lean_object*);
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_ofExcept(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_ofExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adapt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adapt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adapt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adapt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adaptExcept(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_adaptExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_toIO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_toIO_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_toEIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeBaseIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_unsafeBaseIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeEIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_unsafeEIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unsafeIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_unsafeIO(lean_object*, lean_object*);
lean_object* lean_io_timeit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_timeit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_allocprof(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_allocprof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_io_initializing();
LEAN_EXPORT lean_object* l_IO_initializing___boxed(lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_chainTask(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BaseIO_chainTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_bindTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_chainTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_chainTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EIO_mapTasks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_EIO_mapTasks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_lazyPure___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
LEAN_EXPORT lean_object* l_IO_monoMsNow___boxed(lean_object*);
lean_object* lean_io_mono_nanos_now();
LEAN_EXPORT lean_object* l_IO_monoNanosNow___boxed(lean_object*);
lean_object* lean_io_get_random_bytes(size_t);
LEAN_EXPORT lean_object* l_IO_getRandomBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_sleep___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_sleep___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_sleep(uint32_t);
LEAN_EXPORT lean_object* l_IO_sleep___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_bindTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_chainTask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_chainTask(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_chainTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mapTasks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_mapTasks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_io_check_canceled();
LEAN_EXPORT lean_object* l_IO_checkCanceled___boxed(lean_object*);
lean_object* lean_io_cancel(lean_object*);
LEAN_EXPORT lean_object* l_IO_cancel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_instInhabitedTaskState_default;
LEAN_EXPORT uint8_t l_IO_instInhabitedTaskState;
static const lean_string_object l_IO_instReprTaskState_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "IO.TaskState.waiting"};
static const lean_object* l_IO_instReprTaskState_repr___closed__0 = (const lean_object*)&l_IO_instReprTaskState_repr___closed__0_value;
static const lean_ctor_object l_IO_instReprTaskState_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_instReprTaskState_repr___closed__0_value)}};
static const lean_object* l_IO_instReprTaskState_repr___closed__1 = (const lean_object*)&l_IO_instReprTaskState_repr___closed__1_value;
static const lean_string_object l_IO_instReprTaskState_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "IO.TaskState.running"};
static const lean_object* l_IO_instReprTaskState_repr___closed__2 = (const lean_object*)&l_IO_instReprTaskState_repr___closed__2_value;
static const lean_ctor_object l_IO_instReprTaskState_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_instReprTaskState_repr___closed__2_value)}};
static const lean_object* l_IO_instReprTaskState_repr___closed__3 = (const lean_object*)&l_IO_instReprTaskState_repr___closed__3_value;
static const lean_string_object l_IO_instReprTaskState_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "IO.TaskState.finished"};
static const lean_object* l_IO_instReprTaskState_repr___closed__4 = (const lean_object*)&l_IO_instReprTaskState_repr___closed__4_value;
static const lean_ctor_object l_IO_instReprTaskState_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_instReprTaskState_repr___closed__4_value)}};
static const lean_object* l_IO_instReprTaskState_repr___closed__5 = (const lean_object*)&l_IO_instReprTaskState_repr___closed__5_value;
static lean_once_cell_t l_IO_instReprTaskState_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_instReprTaskState_repr___closed__6;
static lean_once_cell_t l_IO_instReprTaskState_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_instReprTaskState_repr___closed__7;
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_instReprTaskState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instReprTaskState_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_instReprTaskState___closed__0 = (const lean_object*)&l_IO_instReprTaskState___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_instReprTaskState = (const lean_object*)&l_IO_instReprTaskState___closed__0_value;
LEAN_EXPORT uint8_t l_IO_TaskState_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_IO_TaskState_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_IO_instDecidableEqTaskState(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_instDecidableEqTaskState___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_instOrdTaskState_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_instOrdTaskState_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_instOrdTaskState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instOrdTaskState_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_instOrdTaskState___closed__0 = (const lean_object*)&l_IO_instOrdTaskState___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_instOrdTaskState = (const lean_object*)&l_IO_instOrdTaskState___closed__0_value;
LEAN_EXPORT lean_object* l_IO_instLTTaskState;
LEAN_EXPORT lean_object* l_IO_instLETaskState;
LEAN_EXPORT uint8_t l_IO_instMinTaskState___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_instMinTaskState___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_instMinTaskState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMinTaskState___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_instMinTaskState___closed__0 = (const lean_object*)&l_IO_instMinTaskState___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_instMinTaskState = (const lean_object*)&l_IO_instMinTaskState___closed__0_value;
LEAN_EXPORT uint8_t l_IO_instMaxTaskState___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_instMaxTaskState___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_instMaxTaskState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMaxTaskState___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_instMaxTaskState___closed__0 = (const lean_object*)&l_IO_instMaxTaskState___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_instMaxTaskState = (const lean_object*)&l_IO_instMaxTaskState___closed__0_value;
static const lean_string_object l_IO_TaskState_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "waiting"};
static const lean_object* l_IO_TaskState_toString___closed__0 = (const lean_object*)&l_IO_TaskState_toString___closed__0_value;
static const lean_string_object l_IO_TaskState_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "running"};
static const lean_object* l_IO_TaskState_toString___closed__1 = (const lean_object*)&l_IO_TaskState_toString___closed__1_value;
static const lean_string_object l_IO_TaskState_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "finished"};
static const lean_object* l_IO_TaskState_toString___closed__2 = (const lean_object*)&l_IO_TaskState_toString___closed__2_value;
LEAN_EXPORT lean_object* l_IO_TaskState_toString(uint8_t);
LEAN_EXPORT lean_object* l_IO_TaskState_toString___boxed(lean_object*);
static const lean_closure_object l_IO_instToStringTaskState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_TaskState_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_instToStringTaskState___closed__0 = (const lean_object*)&l_IO_instToStringTaskState___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_instToStringTaskState = (const lean_object*)&l_IO_instToStringTaskState___closed__0_value;
uint8_t lean_io_get_task_state(lean_object*);
LEAN_EXPORT lean_object* l_IO_getTaskState___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_hasFinished___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_hasFinished___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_hasFinished(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*);
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_waitAny___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_IO_waitAny___auto__1___closed__0 = (const lean_object*)&l_IO_waitAny___auto__1___closed__0_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_IO_waitAny___auto__1___closed__1 = (const lean_object*)&l_IO_waitAny___auto__1___closed__1_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_IO_waitAny___auto__1___closed__2 = (const lean_object*)&l_IO_waitAny___auto__1___closed__2_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_IO_waitAny___auto__1___closed__3 = (const lean_object*)&l_IO_waitAny___auto__1___closed__3_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__4_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__4_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__4_value_aux_2),((lean_object*)&l_IO_waitAny___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_IO_waitAny___auto__1___closed__4 = (const lean_object*)&l_IO_waitAny___auto__1___closed__4_value;
static const lean_array_object l_IO_waitAny___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_IO_waitAny___auto__1___closed__5 = (const lean_object*)&l_IO_waitAny___auto__1___closed__5_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_IO_waitAny___auto__1___closed__6 = (const lean_object*)&l_IO_waitAny___auto__1___closed__6_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__7_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__7_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__7_value_aux_2),((lean_object*)&l_IO_waitAny___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_IO_waitAny___auto__1___closed__7 = (const lean_object*)&l_IO_waitAny___auto__1___closed__7_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_IO_waitAny___auto__1___closed__8 = (const lean_object*)&l_IO_waitAny___auto__1___closed__8_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_IO_waitAny___auto__1___closed__9 = (const lean_object*)&l_IO_waitAny___auto__1___closed__9_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_IO_waitAny___auto__1___closed__10 = (const lean_object*)&l_IO_waitAny___auto__1___closed__10_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__11_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__11_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__11_value_aux_2),((lean_object*)&l_IO_waitAny___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_IO_waitAny___auto__1___closed__11 = (const lean_object*)&l_IO_waitAny___auto__1___closed__11_value;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__12;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__13;
static const lean_string_object l_IO_waitAny___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_IO_waitAny___auto__1___closed__14 = (const lean_object*)&l_IO_waitAny___auto__1___closed__14_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_IO_waitAny___auto__1___closed__15 = (const lean_object*)&l_IO_waitAny___auto__1___closed__15_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__16_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__16_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__16_value_aux_2),((lean_object*)&l_IO_waitAny___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_IO_waitAny___auto__1___closed__16 = (const lean_object*)&l_IO_waitAny___auto__1___closed__16_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Nat.zero_lt_succ"};
static const lean_object* l_IO_waitAny___auto__1___closed__17 = (const lean_object*)&l_IO_waitAny___auto__1___closed__17_value;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__18;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__19;
static const lean_string_object l_IO_waitAny___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_IO_waitAny___auto__1___closed__20 = (const lean_object*)&l_IO_waitAny___auto__1___closed__20_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "zero_lt_succ"};
static const lean_object* l_IO_waitAny___auto__1___closed__21 = (const lean_object*)&l_IO_waitAny___auto__1___closed__21_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__22_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(139, 13, 209, 151, 253, 249, 15, 51)}};
static const lean_object* l_IO_waitAny___auto__1___closed__22 = (const lean_object*)&l_IO_waitAny___auto__1___closed__22_value;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__23;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__24;
static const lean_string_object l_IO_waitAny___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_IO_waitAny___auto__1___closed__25 = (const lean_object*)&l_IO_waitAny___auto__1___closed__25_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__26_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__26_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__26_value_aux_2),((lean_object*)&l_IO_waitAny___auto__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_IO_waitAny___auto__1___closed__26 = (const lean_object*)&l_IO_waitAny___auto__1___closed__26_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_IO_waitAny___auto__1___closed__27 = (const lean_object*)&l_IO_waitAny___auto__1___closed__27_value;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__28;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__29;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__30;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__31;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__32;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__33;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__34;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__35;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__36;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__37;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__38;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__39;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__40;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__41;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__42;
LEAN_EXPORT lean_object* l_IO_waitAny___auto__1;
lean_object* lean_io_wait_any(lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny_x27___auto__1;
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l_IO_waitAny_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_IO_waitAny_x27___redArg___closed__0 = (const lean_object*)&l_IO_waitAny_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_waitAny_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object*);
lean_object* lean_io_set_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_IO_setNumHeartbeats___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_addHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_IO_addHeartbeats___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_instInhabitedStream_default___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_IO_FS_instInhabitedStream_default___lam__0___closed__0 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___lam__0___closed__0_value;
static const lean_ctor_object l_IO_FS_instInhabitedStream_default___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_IO_FS_instInhabitedStream_default___lam__0___closed__0_value)}};
static const lean_object* l_IO_FS_instInhabitedStream_default___lam__0___closed__1 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0();
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1();
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4(size_t);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_FS_instInhabitedStream_default___lam__5(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__5___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instInhabitedStream_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instInhabitedStream_default___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__0 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__0_value;
static const lean_closure_object l_IO_FS_instInhabitedStream_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instInhabitedStream_default___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__1 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__1_value;
static const lean_closure_object l_IO_FS_instInhabitedStream_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instInhabitedStream_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__2 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__2_value;
static const lean_closure_object l_IO_FS_instInhabitedStream_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instInhabitedStream_default___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__3 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__3_value;
static const lean_closure_object l_IO_FS_instInhabitedStream_default___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instInhabitedStream_default___lam__4___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__4 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__4_value;
static const lean_closure_object l_IO_FS_instInhabitedStream_default___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instInhabitedStream_default___lam__5___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__5 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__5_value;
static const lean_ctor_object l_IO_FS_instInhabitedStream_default___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_IO_FS_instInhabitedStream_default___closed__1_value),((lean_object*)&l_IO_FS_instInhabitedStream_default___closed__4_value),((lean_object*)&l_IO_FS_instInhabitedStream_default___closed__3_value),((lean_object*)&l_IO_FS_instInhabitedStream_default___closed__0_value),((lean_object*)&l_IO_FS_instInhabitedStream_default___closed__2_value),((lean_object*)&l_IO_FS_instInhabitedStream_default___closed__5_value)}};
static const lean_object* l_IO_FS_instInhabitedStream_default___closed__6 = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__6_value;
LEAN_EXPORT const lean_object* l_IO_FS_instInhabitedStream_default = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__6_value;
LEAN_EXPORT const lean_object* l_IO_FS_instInhabitedStream = (const lean_object*)&l_IO_FS_instInhabitedStream_default___closed__6_value;
lean_object* lean_get_stdin();
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object*);
lean_object* lean_get_stdout();
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object*);
lean_object* lean_get_stderr();
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object*);
lean_object* lean_get_set_stdin(lean_object*);
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*);
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*);
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_iterate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_iterate___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_iterate(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_iterate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Handle_lock___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_try_lock(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Handle_tryLock___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_unlock(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_unlock___boxed(lean_object*, lean_object*);
uint8_t lean_io_prim_handle_is_tty(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_isTty___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_rewind___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_truncate(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_truncate___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_read(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_FS_Handle_read___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object*, lean_object*);
lean_object* lean_io_remove_dir(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object*, lean_object*);
lean_object* lean_io_create_dir(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object*, lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_rename___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_hard_link(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_hardLink___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_create_tempfile();
LEAN_EXPORT lean_object* l_IO_FS_createTempFile___boxed(lean_object*);
lean_object* lean_io_create_tempdir();
LEAN_EXPORT lean_object* l_IO_FS_createTempDir___boxed(lean_object*);
lean_object* lean_io_getenv(lean_object*);
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object*, lean_object*);
lean_object* lean_io_app_path();
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object*);
lean_object* lean_io_current_dir();
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Handle_readToEnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Tried to read from handle containing non UTF-8 data."};
static const lean_object* l_IO_FS_Handle_readToEnd___closed__0 = (const lean_object*)&l_IO_FS_Handle_readToEnd___closed__0_value;
static const lean_ctor_object l_IO_FS_Handle_readToEnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_IO_FS_Handle_readToEnd___closed__0_value)}};
static const lean_object* l_IO_FS_Handle_readToEnd___closed__1 = (const lean_object*)&l_IO_FS_Handle_readToEnd___closed__1_value;
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_IO_FS_Handle_lines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_IO_FS_Handle_lines___closed__0 = (const lean_object*)&l_IO_FS_Handle_lines___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00IO_FS_instReprDirEntry_repr_spec__0(lean_object*);
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__0 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__0_value;
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "root"};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__1 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__1_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__1_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__2 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__2_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__2_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__3 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__3_value;
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__4 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__4_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__4_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__5 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__3_value),((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__6 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__6_value;
static lean_once_cell_t l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__7;
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__8 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__8_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__8_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__9 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__9_value;
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__10 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__10_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__10_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__11 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__11_value;
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fileName"};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__12 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__12_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__12_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__13 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__13_value;
static lean_once_cell_t l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__14;
static const lean_string_object l_IO_FS_instReprDirEntry_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__15 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__15_value;
static lean_once_cell_t l_IO_FS_instReprDirEntry_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__16;
static lean_once_cell_t l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__17;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__0_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__18 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__18_value;
static const lean_ctor_object l_IO_FS_instReprDirEntry_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__15_value)}};
static const lean_object* l_IO_FS_instReprDirEntry_repr___redArg___closed__19 = (const lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instReprDirEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instReprDirEntry_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instReprDirEntry___closed__0 = (const lean_object*)&l_IO_FS_instReprDirEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instReprDirEntry = (const lean_object*)&l_IO_FS_instReprDirEntry___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_instReprFileType_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "IO.FS.FileType.dir"};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__0 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__0_value;
static const lean_ctor_object l_IO_FS_instReprFileType_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprFileType_repr___closed__0_value)}};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__1 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__1_value;
static const lean_string_object l_IO_FS_instReprFileType_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "IO.FS.FileType.file"};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__2 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__2_value;
static const lean_ctor_object l_IO_FS_instReprFileType_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprFileType_repr___closed__2_value)}};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__3 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__3_value;
static const lean_string_object l_IO_FS_instReprFileType_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "IO.FS.FileType.symlink"};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__4 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__4_value;
static const lean_ctor_object l_IO_FS_instReprFileType_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprFileType_repr___closed__4_value)}};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__5 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__5_value;
static const lean_string_object l_IO_FS_instReprFileType_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "IO.FS.FileType.other"};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__6 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__6_value;
static const lean_ctor_object l_IO_FS_instReprFileType_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprFileType_repr___closed__6_value)}};
static const lean_object* l_IO_FS_instReprFileType_repr___closed__7 = (const lean_object*)&l_IO_FS_instReprFileType_repr___closed__7_value;
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instReprFileType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instReprFileType_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instReprFileType___closed__0 = (const lean_object*)&l_IO_FS_instReprFileType___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instReprFileType = (const lean_object*)&l_IO_FS_instReprFileType___closed__0_value;
LEAN_EXPORT uint8_t l_IO_FS_instBEqFileType_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instBEqFileType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instBEqFileType_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instBEqFileType___closed__0 = (const lean_object*)&l_IO_FS_instBEqFileType___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instBEqFileType = (const lean_object*)&l_IO_FS_instBEqFileType___closed__0_value;
static const lean_string_object l_IO_FS_instReprSystemTime_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sec"};
static const lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__0 = (const lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__0_value;
static const lean_ctor_object l_IO_FS_instReprSystemTime_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__0_value)}};
static const lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__1 = (const lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__1_value;
static const lean_ctor_object l_IO_FS_instReprSystemTime_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__1_value)}};
static const lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__2 = (const lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__2_value;
static const lean_ctor_object l_IO_FS_instReprSystemTime_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__2_value),((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value)}};
static const lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__3 = (const lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__3_value;
static lean_once_cell_t l_IO_FS_instReprSystemTime_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__4;
static const lean_string_object l_IO_FS_instReprSystemTime_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "nsec"};
static const lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__5 = (const lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__5_value;
static const lean_ctor_object l_IO_FS_instReprSystemTime_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__5_value)}};
static const lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__6 = (const lean_object*)&l_IO_FS_instReprSystemTime_repr___redArg___closed__6_value;
static lean_once_cell_t l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instReprSystemTime_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instReprSystemTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instReprSystemTime_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instReprSystemTime___closed__0 = (const lean_object*)&l_IO_FS_instReprSystemTime___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instReprSystemTime = (const lean_object*)&l_IO_FS_instReprSystemTime___closed__0_value;
LEAN_EXPORT uint8_t l_IO_FS_instBEqSystemTime_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instBEqSystemTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instBEqSystemTime_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instBEqSystemTime___closed__0 = (const lean_object*)&l_IO_FS_instBEqSystemTime___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instBEqSystemTime = (const lean_object*)&l_IO_FS_instBEqSystemTime___closed__0_value;
LEAN_EXPORT uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instOrdSystemTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instOrdSystemTime_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instOrdSystemTime___closed__0 = (const lean_object*)&l_IO_FS_instOrdSystemTime___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instOrdSystemTime = (const lean_object*)&l_IO_FS_instOrdSystemTime___closed__0_value;
static lean_once_cell_t l_IO_FS_instInhabitedSystemTime_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_IO_FS_instInhabitedSystemTime_default___closed__0;
static lean_once_cell_t l_IO_FS_instInhabitedSystemTime_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_instInhabitedSystemTime_default___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedSystemTime_default;
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedSystemTime;
LEAN_EXPORT lean_object* l_IO_FS_instLTSystemTime;
LEAN_EXPORT lean_object* l_IO_FS_instLESystemTime;
static const lean_string_object l_IO_FS_instReprMetadata_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "accessed"};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__0 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__0_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__0_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__1 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__1_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__1_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__2 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__2_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__2_value),((lean_object*)&l_IO_FS_instReprDirEntry_repr___redArg___closed__5_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__3 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__3_value;
static const lean_string_object l_IO_FS_instReprMetadata_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "modified"};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__4 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__4_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__4_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__5 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__5_value;
static const lean_string_object l_IO_FS_instReprMetadata_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byteSize"};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__6 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__6_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__6_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__7 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__7_value;
static const lean_string_object l_IO_FS_instReprMetadata_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__8 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__8_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__8_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__9 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__9_value;
static const lean_string_object l_IO_FS_instReprMetadata_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "numLinks"};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__10 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__10_value;
static const lean_ctor_object l_IO_FS_instReprMetadata_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__10_value)}};
static const lean_object* l_IO_FS_instReprMetadata_repr___redArg___closed__11 = (const lean_object*)&l_IO_FS_instReprMetadata_repr___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_instReprMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_instReprMetadata_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_instReprMetadata___closed__0 = (const lean_object*)&l_IO_FS_instReprMetadata___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_FS_instReprMetadata = (const lean_object*)&l_IO_FS_instReprMetadata___closed__0_value;
lean_object* lean_io_read_dir(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object*, lean_object*);
lean_object* lean_io_metadata(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object*, lean_object*);
lean_object* lean_io_symlink_metadata(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_symlinkMetadata___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_System_FilePath_pathExists(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_walkDir___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_IO_FS_readBinFile___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_readBinFile___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_readFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Tried to read file '"};
static const lean_object* l_IO_FS_readFile___closed__0 = (const lean_object*)&l_IO_FS_readFile___closed__0_value;
static const lean_string_object l_IO_FS_readFile___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' containing non UTF-8 data."};
static const lean_object* l_IO_FS_readFile___closed__1 = (const lean_object*)&l_IO_FS_readFile___closed__1_value;
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_IO_withStdin___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_withStdin___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_withStdin___redArg___closed__0 = (const lean_object*)&l_IO_withStdin___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_withStdin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_IO_println___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_println___redArg___closed__0 = (const lean_object*)&l_IO_println___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_println___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_io_eprint(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintlnAux___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_appDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "IO.appDir: unexpected filename '"};
static const lean_object* l_IO_appDir___closed__0 = (const lean_object*)&l_IO_appDir___closed__0_value;
static const lean_string_object l_IO_appDir___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_IO_appDir___closed__1 = (const lean_object*)&l_IO_appDir___closed__1_value;
LEAN_EXPORT lean_object* l_IO_appDir();
LEAN_EXPORT lean_object* l_IO_appDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_withTempFile___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_createTempFile___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_withTempFile___redArg___closed__0 = (const lean_object*)&l_IO_FS_withTempFile___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_withTempDir___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_createTempDir___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_FS_withTempDir___redArg___closed__0 = (const lean_object*)&l_IO_FS_withTempDir___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_get_current_dir();
LEAN_EXPORT lean_object* l_IO_Process_getCurrentDir___boxed(lean_object*);
lean_object* lean_io_process_set_current_dir(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_setCurrentDir___boxed(lean_object*, lean_object*);
uint32_t lean_io_process_get_pid();
LEAN_EXPORT lean_object* l_IO_Process_getPID___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_try_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_tryWait___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_kill(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_kill___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_take_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_io_process_child_pid(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_Child_pid___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_IO_Process_output___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_IO_Process_output___closed__0 = (const lean_object*)&l_IO_Process_output___closed__0_value;
static const lean_ctor_object l_IO_Process_output___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_IO_Process_output___closed__1 = (const lean_object*)&l_IO_Process_output___closed__1_value;
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_output___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_Process_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "process '"};
static const lean_object* l_IO_Process_run___closed__0 = (const lean_object*)&l_IO_Process_run___closed__0_value;
static const lean_string_object l_IO_Process_run___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' exited with code "};
static const lean_object* l_IO_Process_run___closed__1 = (const lean_object*)&l_IO_Process_run___closed__1_value;
static const lean_string_object l_IO_Process_run___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nstderr:\n"};
static const lean_object* l_IO_Process_run___closed__2 = (const lean_object*)&l_IO_Process_run___closed__2_value;
LEAN_EXPORT lean_object* l_IO_Process_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Process_run___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_exit(uint8_t);
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_force_exit(uint8_t);
LEAN_EXPORT lean_object* l_IO_Process_forceExit___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_io_get_tid();
LEAN_EXPORT lean_object* l_IO_getTID___boxed(lean_object*);
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object*);
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object*);
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object*);
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object*);
lean_object* lean_chmod(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_IO_instMonadLiftSTRealWorldBaseIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___closed__0 = (const lean_object*)&l_IO_instMonadLiftSTRealWorldBaseIO___closed__0_value;
LEAN_EXPORT const lean_object* l_IO_instMonadLiftSTRealWorldBaseIO = (const lean_object*)&l_IO_instMonadLiftSTRealWorldBaseIO___closed__0_value;
LEAN_EXPORT lean_object* l_IO_mkRef___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_mkRef___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_mkRef___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_new();
LEAN_EXPORT lean_object* l_IO_CancelToken_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_set(lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_set___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_CancelToken_isSet(lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_isSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_io_cancel_token_is_set(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_CancelToken_isSetExport___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_ofBuffer___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invalid UTF-8"};
static const lean_object* l_IO_FS_Stream_ofBuffer___lam__3___closed__0 = (const lean_object*)&l_IO_FS_Stream_ofBuffer___lam__3___closed__0_value;
static const lean_ctor_object l_IO_FS_Stream_ofBuffer___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_IO_FS_Stream_ofBuffer___lam__3___closed__0_value)}};
static const lean_object* l_IO_FS_Stream_ofBuffer___lam__3___closed__1 = (const lean_object*)&l_IO_FS_Stream_ofBuffer___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4___boxed(lean_object*, lean_object*);
static const lean_closure_object l_IO_FS_Stream_ofBuffer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_FS_Stream_ofBuffer___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_IO_FS_Stream_ofBuffer___closed__0 = (const lean_object*)&l_IO_FS_Stream_ofBuffer___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
static const lean_ctor_object l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(1024ULL)}};
LEAN_EXPORT const lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1 = (const lean_object*)&l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readToEnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Tried to read from stream containing non UTF-8 data."};
static const lean_object* l_IO_FS_Stream_readToEnd___closed__0 = (const lean_object*)&l_IO_FS_Stream_readToEnd___closed__0_value;
static const lean_ctor_object l_IO_FS_Stream_readToEnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_IO_FS_Stream_readToEnd___closed__0_value)}};
static const lean_object* l_IO_FS_Stream_readToEnd___closed__1 = (const lean_object*)&l_IO_FS_Stream_readToEnd___closed__1_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0 = (const lean_object*)&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0_value;
static const lean_string_object l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1 = (const lean_object*)&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1_value;
static const lean_string_object l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2 = (const lean_object*)&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2_value;
static const lean_string_object l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3 = (const lean_object*)&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3_value;
static lean_once_cell_t l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_IO_FS_withIsolatedStreams___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_withIsolatedStreams___redArg___closed__0;
static lean_once_cell_t l_IO_FS_withIsolatedStreams___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_withIsolatedStreams___redArg___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_termPrintln_x21_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termPrintln!__"};
static const lean_object* l_termPrintln_x21_____00__closed__0 = (const lean_object*)&l_termPrintln_x21_____00__closed__0_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termPrintln_x21_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 121, 220, 17, 1, 74, 122, 9)}};
static const lean_object* l_termPrintln_x21_____00__closed__1 = (const lean_object*)&l_termPrintln_x21_____00__closed__1_value;
static const lean_string_object l_termPrintln_x21_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_termPrintln_x21_____00__closed__2 = (const lean_object*)&l_termPrintln_x21_____00__closed__2_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termPrintln_x21_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_termPrintln_x21_____00__closed__3 = (const lean_object*)&l_termPrintln_x21_____00__closed__3_value;
static const lean_string_object l_termPrintln_x21_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "println! "};
static const lean_object* l_termPrintln_x21_____00__closed__4 = (const lean_object*)&l_termPrintln_x21_____00__closed__4_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_termPrintln_x21_____00__closed__4_value)}};
static const lean_object* l_termPrintln_x21_____00__closed__5 = (const lean_object*)&l_termPrintln_x21_____00__closed__5_value;
static const lean_string_object l_termPrintln_x21_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_termPrintln_x21_____00__closed__6 = (const lean_object*)&l_termPrintln_x21_____00__closed__6_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termPrintln_x21_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_termPrintln_x21_____00__closed__7 = (const lean_object*)&l_termPrintln_x21_____00__closed__7_value;
static const lean_string_object l_termPrintln_x21_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_termPrintln_x21_____00__closed__8 = (const lean_object*)&l_termPrintln_x21_____00__closed__8_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termPrintln_x21_____00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l_termPrintln_x21_____00__closed__9 = (const lean_object*)&l_termPrintln_x21_____00__closed__9_value;
static const lean_string_object l_termPrintln_x21_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_termPrintln_x21_____00__closed__10 = (const lean_object*)&l_termPrintln_x21_____00__closed__10_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termPrintln_x21_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_termPrintln_x21_____00__closed__11 = (const lean_object*)&l_termPrintln_x21_____00__closed__11_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_termPrintln_x21_____00__closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_termPrintln_x21_____00__closed__12 = (const lean_object*)&l_termPrintln_x21_____00__closed__12_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_termPrintln_x21_____00__closed__9_value),((lean_object*)&l_termPrintln_x21_____00__closed__12_value)}};
static const lean_object* l_termPrintln_x21_____00__closed__13 = (const lean_object*)&l_termPrintln_x21_____00__closed__13_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_termPrintln_x21_____00__closed__7_value),((lean_object*)&l_termPrintln_x21_____00__closed__13_value),((lean_object*)&l_termPrintln_x21_____00__closed__12_value)}};
static const lean_object* l_termPrintln_x21_____00__closed__14 = (const lean_object*)&l_termPrintln_x21_____00__closed__14_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_termPrintln_x21_____00__closed__3_value),((lean_object*)&l_termPrintln_x21_____00__closed__5_value),((lean_object*)&l_termPrintln_x21_____00__closed__14_value)}};
static const lean_object* l_termPrintln_x21_____00__closed__15 = (const lean_object*)&l_termPrintln_x21_____00__closed__15_value;
static const lean_ctor_object l_termPrintln_x21_____00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_termPrintln_x21_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_termPrintln_x21_____00__closed__15_value)}};
static const lean_object* l_termPrintln_x21_____00__closed__16 = (const lean_object*)&l_termPrintln_x21_____00__closed__16_value;
LEAN_EXPORT const lean_object* l_termPrintln_x21____ = (const lean_object*)&l_termPrintln_x21_____00__closed__16_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value_aux_2),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value_aux_2),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8_value;
static lean_once_cell_t l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "System"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__12_value)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__10_value),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__14_value)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "IO.println"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16_value;
static lean_once_cell_t l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "IO"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "println"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(2, 76, 19, 202, 4, 69, 238, 60)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value_aux_0),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(113, 81, 230, 194, 109, 88, 193, 19)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23_value;
static lean_once_cell_t l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(2, 76, 19, 202, 4, 69, 238, 60)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25_value)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__26_value),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__28_value)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30_value;
static lean_once_cell_t l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32_value)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__33_value),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__35_value)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value_aux_2),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termS!_"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40_value;
static const lean_ctor_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(30, 130, 93, 49, 63, 146, 201, 153)}};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41_value;
static const lean_string_object l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "s!"};
static const lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42 = (const lean_object*)&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42_value;
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_runtime_mark_multi_threaded(lean_object*);
LEAN_EXPORT lean_object* l_Runtime_markMultiThreaded___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_runtime_mark_persistent(lean_object*);
LEAN_EXPORT lean_object* l_Runtime_markPersistent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_runtime_forget(lean_object*);
LEAN_EXPORT lean_object* l_Runtime_forget___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_runtime_hold(lean_object*);
LEAN_EXPORT lean_object* l_Runtime_hold___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_IO_RealWorld_nonemptyType(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__1___redArg(lean_object* v_f_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_1(v_x_3_, lean_box(0));
v___x_6_ = lean_apply_1(v_f_2_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__1___redArg___boxed(lean_object* v_f_7_, lean_object* v_x_8_, lean_object* v_a_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_instMonadBaseIO___aux__1___redArg(v_f_7_, v_x_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__1(lean_object* v_00_u03b1_11_, lean_object* v_00_u03b2_12_, lean_object* v_f_13_, lean_object* v_x_14_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_apply_1(v_x_14_, lean_box(0));
v___x_17_ = lean_apply_1(v_f_13_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__1___boxed(lean_object* v_00_u03b1_18_, lean_object* v_00_u03b2_19_, lean_object* v_f_20_, lean_object* v_x_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_instMonadBaseIO___aux__1(v_00_u03b1_18_, v_00_u03b2_19_, v_f_20_, v_x_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__3___redArg(lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_apply_1(v_a_25_, lean_box(0));
lean_dec(v___x_27_);
lean_inc(v_a_24_);
return v_a_24_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__3___redArg___boxed(lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_instMonadBaseIO___aux__3___redArg(v_a_28_, v_a_29_);
lean_dec(v_a_28_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__3(lean_object* v_00_u03b1_32_, lean_object* v_00_u03b2_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_apply_1(v_a_35_, lean_box(0));
lean_dec(v___x_37_);
lean_inc(v_a_34_);
return v_a_34_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__3___boxed(lean_object* v_00_u03b1_38_, lean_object* v_00_u03b2_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_instMonadBaseIO___aux__3(v_00_u03b1_38_, v_00_u03b2_39_, v_a_40_, v_a_41_);
lean_dec(v_a_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__5___redArg(lean_object* v_x_44_){
_start:
{
lean_inc(v_x_44_);
return v_x_44_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__5___redArg___boxed(lean_object* v_x_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_instMonadBaseIO___aux__5___redArg(v_x_46_);
lean_dec(v_x_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__5(lean_object* v_00_u03b1_49_, lean_object* v_x_50_){
_start:
{
lean_inc(v_x_50_);
return v_x_50_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__5___boxed(lean_object* v_00_u03b1_52_, lean_object* v_x_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_instMonadBaseIO___aux__5(v_00_u03b1_52_, v_x_53_);
lean_dec(v_x_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__7___redArg(lean_object* v_f_56_, lean_object* v_x_57_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = lean_apply_1(v_f_56_, lean_box(0));
v___x_60_ = lean_box(0);
v___x_61_ = lean_apply_2(v_x_57_, v___x_60_, lean_box(0));
v___x_62_ = lean_apply_1(v___x_59_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__7___redArg___boxed(lean_object* v_f_63_, lean_object* v_x_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_instMonadBaseIO___aux__7___redArg(v_f_63_, v_x_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__7(lean_object* v_00_u03b1_67_, lean_object* v_00_u03b2_68_, lean_object* v_f_69_, lean_object* v_x_70_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_72_ = lean_apply_1(v_f_69_, lean_box(0));
v___x_73_ = lean_box(0);
v___x_74_ = lean_apply_2(v_x_70_, v___x_73_, lean_box(0));
v___x_75_ = lean_apply_1(v___x_72_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__7___boxed(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_f_78_, lean_object* v_x_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_instMonadBaseIO___aux__7(v_00_u03b1_76_, v_00_u03b2_77_, v_f_78_, v_x_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__9___redArg(lean_object* v_x_82_, lean_object* v_y_83_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_apply_1(v_x_82_, lean_box(0));
v___x_86_ = lean_box(0);
v___x_87_ = lean_apply_2(v_y_83_, v___x_86_, lean_box(0));
lean_dec(v___x_87_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__9___redArg___boxed(lean_object* v_x_88_, lean_object* v_y_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_instMonadBaseIO___aux__9___redArg(v_x_88_, v_y_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__9(lean_object* v_00_u03b1_92_, lean_object* v_00_u03b2_93_, lean_object* v_x_94_, lean_object* v_y_95_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_apply_1(v_x_94_, lean_box(0));
v___x_98_ = lean_box(0);
v___x_99_ = lean_apply_2(v_y_95_, v___x_98_, lean_box(0));
lean_dec(v___x_99_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__9___boxed(lean_object* v_00_u03b1_100_, lean_object* v_00_u03b2_101_, lean_object* v_x_102_, lean_object* v_y_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_instMonadBaseIO___aux__9(v_00_u03b1_100_, v_00_u03b2_101_, v_x_102_, v_y_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__11___redArg(lean_object* v_x_106_, lean_object* v_y_107_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_apply_1(v_x_106_, lean_box(0));
lean_dec(v___x_109_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_apply_2(v_y_107_, v___x_110_, lean_box(0));
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__11___redArg___boxed(lean_object* v_x_112_, lean_object* v_y_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_instMonadBaseIO___aux__11___redArg(v_x_112_, v_y_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__11(lean_object* v_00_u03b1_116_, lean_object* v_00_u03b2_117_, lean_object* v_x_118_, lean_object* v_y_119_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_apply_1(v_x_118_, lean_box(0));
lean_dec(v___x_121_);
v___x_122_ = lean_box(0);
v___x_123_ = lean_apply_2(v_y_119_, v___x_122_, lean_box(0));
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__11___boxed(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_x_126_, lean_object* v_y_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_instMonadBaseIO___aux__11(v_00_u03b1_124_, v_00_u03b2_125_, v_x_126_, v_y_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__13___redArg(lean_object* v_x_130_, lean_object* v_f_131_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_apply_1(v_x_130_, lean_box(0));
v___x_134_ = lean_apply_2(v_f_131_, v___x_133_, lean_box(0));
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__13___redArg___boxed(lean_object* v_x_135_, lean_object* v_f_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_instMonadBaseIO___aux__13___redArg(v_x_135_, v_f_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__13(lean_object* v_00_u03b1_139_, lean_object* v_00_u03b2_140_, lean_object* v_x_141_, lean_object* v_f_142_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_apply_1(v_x_141_, lean_box(0));
v___x_145_ = lean_apply_2(v_f_142_, v___x_144_, lean_box(0));
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__13___boxed(lean_object* v_00_u03b1_146_, lean_object* v_00_u03b2_147_, lean_object* v_x_148_, lean_object* v_f_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_instMonadBaseIO___aux__13(v_00_u03b1_146_, v_00_u03b2_147_, v_x_148_, v_f_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO___aux__1___redArg(lean_object* v_x_172_, lean_object* v_f_173_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = lean_apply_1(v_x_172_, lean_box(0));
lean_inc(v___x_175_);
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
v___x_177_ = lean_apply_2(v_f_173_, v___x_176_, lean_box(0));
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_175_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO___aux__1___redArg___boxed(lean_object* v_x_179_, lean_object* v_f_180_, lean_object* v_s_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_instMonadFinallyBaseIO___aux__1___redArg(v_x_179_, v_f_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO___aux__1(lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_x_185_, lean_object* v_f_186_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = lean_apply_1(v_x_185_, lean_box(0));
lean_inc(v___x_188_);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
v___x_190_ = lean_apply_2(v_f_186_, v___x_189_, lean_box(0));
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_188_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO___aux__1___boxed(lean_object* v_00_u03b1_192_, lean_object* v_00_u03b2_193_, lean_object* v_x_194_, lean_object* v_f_195_, lean_object* v_s_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_instMonadFinallyBaseIO___aux__1(v_00_u03b1_192_, v_00_u03b2_193_, v_x_194_, v_f_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachBaseIO___aux__3___redArg(lean_object* v_x_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_apply_1(v_x_200_, lean_box(0));
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachBaseIO___aux__3___redArg___boxed(lean_object* v_x_203_, lean_object* v_s_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_instMonadAttachBaseIO___aux__3___redArg(v_x_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachBaseIO___aux__3(lean_object* v_00_u03b1_206_, lean_object* v_x_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_apply_1(v_x_207_, lean_box(0));
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachBaseIO___aux__3___boxed(lean_object* v_00_u03b1_210_, lean_object* v_x_211_, lean_object* v_s_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_instMonadAttachBaseIO___aux__3(v_00_u03b1_210_, v_x_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_map___redArg(lean_object* v_f_216_, lean_object* v_x_217_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_apply_1(v_x_217_, lean_box(0));
v___x_220_ = lean_apply_1(v_f_216_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_map___redArg___boxed(lean_object* v_f_221_, lean_object* v_x_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_BaseIO_map___redArg(v_f_221_, v_x_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_map(lean_object* v_00_u03b1_225_, lean_object* v_00_u03b2_226_, lean_object* v_f_227_, lean_object* v_x_228_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_apply_1(v_x_228_, lean_box(0));
v___x_231_ = lean_apply_1(v_f_227_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_map___boxed(lean_object* v_00_u03b1_232_, lean_object* v_00_u03b2_233_, lean_object* v_f_234_, lean_object* v_x_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_BaseIO_map(v_00_u03b1_232_, v_00_u03b2_233_, v_f_234_, v_x_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg(lean_object* v_act_238_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_apply_1(v_act_238_, lean_box(0));
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg___boxed(lean_object* v_act_242_, lean_object* v_s_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_BaseIO_toEIO___redArg(v_act_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b5_246_, lean_object* v_act_247_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_apply_1(v_act_247_, lean_box(0));
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___boxed(lean_object* v_00_u03b1_251_, lean_object* v_00_u03b5_252_, lean_object* v_act_253_, lean_object* v_s_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_BaseIO_toEIO(v_00_u03b1_251_, v_00_u03b5_252_, v_act_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0(lean_object* v_00_u03b1_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_apply_1(v___y_257_, lean_box(0));
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object* v_00_u03b1_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_instMonadLiftBaseIOEIO___lam__0(v_00_u03b1_261_, v___y_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object* v_00_u03b5_266_){
_start:
{
lean_object* v___f_267_; 
v___f_267_ = ((lean_object*)(l_instMonadLiftBaseIOEIO___closed__0));
return v___f_267_;
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg(lean_object* v_act_268_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = lean_apply_1(v_act_268_, lean_box(0));
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set_tag(v___x_273_, 1);
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
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v_a_279_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_270_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_270_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 0);
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg___boxed(lean_object* v_act_287_, lean_object* v_s_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_EIO_toBaseIO___redArg(v_act_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO(lean_object* v_00_u03b5_290_, lean_object* v_00_u03b1_291_, lean_object* v_act_292_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lean_apply_1(v_act_292_, lean_box(0));
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_294_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set_tag(v___x_297_, 1);
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_a_303_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_294_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_294_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 0);
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___boxed(lean_object* v_00_u03b5_311_, lean_object* v_00_u03b1_312_, lean_object* v_act_313_, lean_object* v_s_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_EIO_toBaseIO(v_00_u03b5_311_, v_00_u03b1_312_, v_act_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg(lean_object* v_act_316_, lean_object* v_h_317_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_apply_1(v_act_316_, lean_box(0));
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; 
lean_dec_ref(v_h_317_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref(v___x_319_);
return v_a_320_;
}
else
{
lean_object* v_a_321_; lean_object* v___x_322_; 
v_a_321_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_321_);
lean_dec_ref(v___x_319_);
v___x_322_ = lean_apply_2(v_h_317_, v_a_321_, lean_box(0));
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg___boxed(lean_object* v_act_323_, lean_object* v_h_324_, lean_object* v_s_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_EIO_catchExceptions___redArg(v_act_323_, v_h_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions(lean_object* v_00_u03b5_327_, lean_object* v_00_u03b1_328_, lean_object* v_act_329_, lean_object* v_h_330_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = lean_apply_1(v_act_329_, lean_box(0));
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; 
lean_dec_ref(v_h_330_);
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref(v___x_332_);
return v_a_333_;
}
else
{
lean_object* v_a_334_; lean_object* v___x_335_; 
v_a_334_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_334_);
lean_dec_ref(v___x_332_);
v___x_335_ = lean_apply_2(v_h_330_, v_a_334_, lean_box(0));
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___boxed(lean_object* v_00_u03b5_336_, lean_object* v_00_u03b1_337_, lean_object* v_act_338_, lean_object* v_h_339_, lean_object* v_s_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_EIO_catchExceptions(v_00_u03b5_336_, v_00_u03b1_337_, v_act_338_, v_h_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1___redArg(lean_object* v_f_342_, lean_object* v_x_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lean_apply_1(v_x_343_, lean_box(0));
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_354_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_354_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_apply_1(v_f_342_, v_a_346_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec(v_f_342_);
v_a_355_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_345_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_345_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1___redArg___boxed(lean_object* v_f_363_, lean_object* v_x_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_instMonadEIO___aux__1___redArg(v_f_363_, v_x_364_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1(lean_object* v_00_u03b5_367_, lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_f_370_, lean_object* v_x_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_apply_1(v_x_371_, lean_box(0));
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_382_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_382_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = lean_apply_1(v_f_370_, v_a_374_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_f_370_);
v_a_383_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_373_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_373_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1___boxed(lean_object* v_00_u03b5_391_, lean_object* v_00_u03b1_392_, lean_object* v_00_u03b2_393_, lean_object* v_f_394_, lean_object* v_x_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_instMonadEIO___aux__1(v_00_u03b5_391_, v_00_u03b1_392_, v_00_u03b2_393_, v_f_394_, v_x_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3___redArg(lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = lean_apply_1(v_a_399_, lean_box(0));
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
lean_ctor_set(v___x_403_, 0, v_a_398_);
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_398_);
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
lean_dec(v_a_398_);
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
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3___redArg___boxed(lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_instMonadEIO___aux__3___redArg(v_a_418_, v_a_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3(lean_object* v_00_u03b5_422_, lean_object* v_00_u03b1_423_, lean_object* v_00_u03b2_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = lean_apply_1(v_a_426_, lean_box(0));
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; 
v_unused_436_ = lean_ctor_get(v___x_428_, 0);
lean_dec(v_unused_436_);
v___x_430_ = v___x_428_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_dec(v___x_428_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v_a_425_);
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_425_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec(v_a_425_);
v_a_437_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_428_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_428_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3___boxed(lean_object* v_00_u03b5_445_, lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_instMonadEIO___aux__3(v_00_u03b5_445_, v_00_u03b1_446_, v_00_u03b2_447_, v_a_448_, v_a_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5___redArg(lean_object* v_a_452_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v_a_452_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5___redArg___boxed(lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_instMonadEIO___aux__5___redArg(v_a_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5(lean_object* v_00_u03b5_458_, lean_object* v_00_u03b1_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v_a_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5___boxed(lean_object* v_00_u03b5_463_, lean_object* v_00_u03b1_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_instMonadEIO___aux__5(v_00_u03b5_463_, v_00_u03b1_464_, v_a_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7___redArg(lean_object* v_f_468_, lean_object* v_x_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = lean_apply_1(v_f_468_, lean_box(0));
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref(v___x_471_);
v___x_473_ = lean_box(0);
v___x_474_ = lean_apply_2(v_x_469_, v___x_473_, lean_box(0));
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_483_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_483_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = lean_apply_1(v_a_472_, v_a_475_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_479_);
v___x_481_ = v___x_477_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec(v_a_472_);
v_a_484_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_474_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_474_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec_ref(v_x_469_);
v_a_492_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_471_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_471_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7___redArg___boxed(lean_object* v_f_500_, lean_object* v_x_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_instMonadEIO___aux__7___redArg(v_f_500_, v_x_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7(lean_object* v_00_u03b5_504_, lean_object* v_00_u03b1_505_, lean_object* v_00_u03b2_506_, lean_object* v_f_507_, lean_object* v_x_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_apply_1(v_f_507_, lean_box(0));
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v___x_510_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_apply_2(v_x_508_, v___x_512_, lean_box(0));
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_522_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_522_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = lean_apply_1(v_a_511_, v_a_514_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_a_511_);
v_a_523_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_513_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_513_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref(v_x_508_);
v_a_531_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_510_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_510_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7___boxed(lean_object* v_00_u03b5_539_, lean_object* v_00_u03b1_540_, lean_object* v_00_u03b2_541_, lean_object* v_f_542_, lean_object* v_x_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_instMonadEIO___aux__7(v_00_u03b5_539_, v_00_u03b1_540_, v_00_u03b2_541_, v_f_542_, v_x_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9___redArg(lean_object* v_x_546_, lean_object* v_y_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = lean_apply_1(v_x_546_, lean_box(0));
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref(v___x_549_);
v___x_551_ = lean_box(0);
v___x_552_ = lean_apply_2(v_y_547_, v___x_551_, lean_box(0));
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v___x_552_, 0);
lean_dec(v_unused_560_);
v___x_554_ = v___x_552_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_dec(v___x_552_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v_a_550_);
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_550_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v_a_550_);
v_a_561_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_552_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_552_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_dec_ref(v_y_547_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9___redArg___boxed(lean_object* v_x_569_, lean_object* v_y_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_instMonadEIO___aux__9___redArg(v_x_569_, v_y_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9(lean_object* v_00_u03b5_573_, lean_object* v_00_u03b1_574_, lean_object* v_00_u03b2_575_, lean_object* v_x_576_, lean_object* v_y_577_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = lean_apply_1(v_x_576_, lean_box(0));
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref(v___x_579_);
v___x_581_ = lean_box(0);
v___x_582_ = lean_apply_2(v_y_577_, v___x_581_, lean_box(0));
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; 
v_unused_590_ = lean_ctor_get(v___x_582_, 0);
lean_dec(v_unused_590_);
v___x_584_ = v___x_582_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_dec(v___x_582_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v_a_580_);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_580_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec(v_a_580_);
v_a_591_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_582_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_582_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
else
{
lean_dec_ref(v_y_577_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9___boxed(lean_object* v_00_u03b5_599_, lean_object* v_00_u03b1_600_, lean_object* v_00_u03b2_601_, lean_object* v_x_602_, lean_object* v_y_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_instMonadEIO___aux__9(v_00_u03b5_599_, v_00_u03b1_600_, v_00_u03b2_601_, v_x_602_, v_y_603_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11___redArg(lean_object* v_x_606_, lean_object* v_y_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_apply_1(v_x_606_, lean_box(0));
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec_ref(v___x_609_);
v___x_610_ = lean_box(0);
v___x_611_ = lean_apply_2(v_y_607_, v___x_610_, lean_box(0));
return v___x_611_;
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec_ref(v_y_607_);
v_a_612_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_609_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_609_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11___redArg___boxed(lean_object* v_x_620_, lean_object* v_y_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_instMonadEIO___aux__11___redArg(v_x_620_, v_y_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11(lean_object* v_00_u03b5_624_, lean_object* v_00_u03b1_625_, lean_object* v_00_u03b2_626_, lean_object* v_x_627_, lean_object* v_y_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_apply_1(v_x_627_, lean_box(0));
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec_ref(v___x_630_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_apply_2(v_y_628_, v___x_631_, lean_box(0));
return v___x_632_;
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec_ref(v_y_628_);
v_a_633_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_630_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_630_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11___boxed(lean_object* v_00_u03b5_641_, lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_x_644_, lean_object* v_y_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_instMonadEIO___aux__11(v_00_u03b5_641_, v_00_u03b1_642_, v_00_u03b2_643_, v_x_644_, v_y_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13___redArg(lean_object* v_x_648_, lean_object* v_f_649_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = lean_apply_1(v_x_648_, lean_box(0));
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref(v___x_651_);
v___x_653_ = lean_apply_2(v_f_649_, v_a_652_, lean_box(0));
return v___x_653_;
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v_f_649_);
v_a_654_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_651_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_651_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13___redArg___boxed(lean_object* v_x_662_, lean_object* v_f_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_instMonadEIO___aux__13___redArg(v_x_662_, v_f_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13(lean_object* v_00_u03b5_666_, lean_object* v_00_u03b1_667_, lean_object* v_00_u03b2_668_, lean_object* v_x_669_, lean_object* v_f_670_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = lean_apply_1(v_x_669_, lean_box(0));
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_674_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref(v___x_672_);
v___x_674_ = lean_apply_2(v_f_670_, v_a_673_, lean_box(0));
return v___x_674_;
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v_f_670_);
v_a_675_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_672_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_672_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13___boxed(lean_object* v_00_u03b5_683_, lean_object* v_00_u03b1_684_, lean_object* v_00_u03b2_685_, lean_object* v_x_686_, lean_object* v_f_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_instMonadEIO___aux__13(v_00_u03b5_683_, v_00_u03b1_684_, v_00_u03b2_685_, v_x_686_, v_f_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object* v_00_u03b5_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = ((lean_object*)(l_instMonadEIO___closed__9));
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___redArg(lean_object* v_x_711_, lean_object* v_f_712_){
_start:
{
lean_object* v_r_714_; 
v_r_714_ = lean_apply_1(v_x_711_, lean_box(0));
if (lean_obj_tag(v_r_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_740_; 
v_a_715_ = lean_ctor_get(v_r_714_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v_r_714_);
if (v_isSharedCheck_740_ == 0)
{
v___x_717_ = v_r_714_;
v_isShared_718_ = v_isSharedCheck_740_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v_r_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_740_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
lean_inc(v_a_715_);
if (v_isShared_718_ == 0)
{
lean_ctor_set_tag(v___x_717_, 1);
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_739_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; 
v___x_721_ = lean_apply_2(v_f_712_, v___x_720_, lean_box(0));
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_730_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_730_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_a_715_);
lean_ctor_set(v___x_726_, 1, v_a_722_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_726_);
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v_a_715_);
v_a_731_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_721_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_721_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_a_741_ = lean_ctor_get(v_r_714_, 0);
lean_inc(v_a_741_);
lean_dec_ref(v_r_714_);
v___x_742_ = lean_box(0);
v___x_743_ = lean_apply_2(v_f_712_, v___x_742_, lean_box(0));
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v___x_743_, 0);
lean_dec(v_unused_751_);
v___x_745_ = v___x_743_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_dec(v___x_743_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 1);
lean_ctor_set(v___x_745_, 0, v_a_741_);
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_741_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_a_741_);
v_a_752_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_743_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_743_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___redArg___boxed(lean_object* v_x_760_, lean_object* v_f_761_, lean_object* v_s_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_instMonadFinallyEIO___aux__1___redArg(v_x_760_, v_f_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1(lean_object* v_00_u03b5_764_, lean_object* v_00_u03b1_765_, lean_object* v_00_u03b2_766_, lean_object* v_x_767_, lean_object* v_f_768_){
_start:
{
lean_object* v_r_770_; 
v_r_770_ = lean_apply_1(v_x_767_, lean_box(0));
if (lean_obj_tag(v_r_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_796_; 
v_a_771_ = lean_ctor_get(v_r_770_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_r_770_);
if (v_isSharedCheck_796_ == 0)
{
v___x_773_ = v_r_770_;
v_isShared_774_ = v_isSharedCheck_796_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v_r_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_796_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
lean_inc(v_a_771_);
if (v_isShared_774_ == 0)
{
lean_ctor_set_tag(v___x_773_, 1);
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_795_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; 
v___x_777_ = lean_apply_2(v_f_768_, v___x_776_, lean_box(0));
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_786_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_786_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_a_771_);
lean_ctor_set(v___x_782_, 1, v_a_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_a_771_);
v_a_787_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_777_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_777_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_a_797_ = lean_ctor_get(v_r_770_, 0);
lean_inc(v_a_797_);
lean_dec_ref(v_r_770_);
v___x_798_ = lean_box(0);
v___x_799_ = lean_apply_2(v_f_768_, v___x_798_, lean_box(0));
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v___x_799_, 0);
lean_dec(v_unused_807_);
v___x_801_ = v___x_799_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_dec(v___x_799_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 1);
lean_ctor_set(v___x_801_, 0, v_a_797_);
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_797_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v_a_797_);
v_a_808_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_799_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_799_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___boxed(lean_object* v_00_u03b5_816_, lean_object* v_00_u03b1_817_, lean_object* v_00_u03b2_818_, lean_object* v_x_819_, lean_object* v_f_820_, lean_object* v_s_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_instMonadFinallyEIO___aux__1(v_00_u03b5_816_, v_00_u03b1_817_, v_00_u03b2_818_, v_x_819_, v_f_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object* v_00_u03b5_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = ((lean_object*)(l_instMonadFinallyEIO___closed__0));
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___redArg(lean_object* v_x_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = lean_apply_1(v_x_826_, lean_box(0));
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
v_a_837_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_828_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_828_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___redArg___boxed(lean_object* v_x_845_, lean_object* v_s_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_instMonadAttachEIO___aux__3___redArg(v_x_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3(lean_object* v_00_u03b5_848_, lean_object* v_00_u03b1_849_, lean_object* v_x_850_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = lean_apply_1(v_x_850_, lean_box(0));
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
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_a_861_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_852_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_852_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___boxed(lean_object* v_00_u03b5_869_, lean_object* v_00_u03b1_870_, lean_object* v_x_871_, lean_object* v_s_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_instMonadAttachEIO___aux__3(v_00_u03b5_869_, v_00_u03b1_870_, v_x_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO(lean_object* v_00_u03b5_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = ((lean_object*)(l_instMonadAttachEIO___closed__0));
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___redArg(lean_object* v_e_877_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_879_, 0, v_e_877_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___redArg___boxed(lean_object* v_e_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_instMonadExceptOfEIO___aux__1___redArg(v_e_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1(lean_object* v_00_u03b5_883_, lean_object* v_00_u03b1_884_, lean_object* v_e_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v_e_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___boxed(lean_object* v_00_u03b5_888_, lean_object* v_00_u03b1_889_, lean_object* v_e_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_instMonadExceptOfEIO___aux__1(v_00_u03b5_888_, v_00_u03b1_889_, v_e_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___redArg(lean_object* v_x_893_, lean_object* v_handle_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_apply_1(v_x_893_, lean_box(0));
if (lean_obj_tag(v___x_896_) == 0)
{
lean_dec_ref(v_handle_894_);
return v___x_896_;
}
else
{
lean_object* v_a_897_; lean_object* v___x_898_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref(v___x_896_);
v___x_898_ = lean_apply_2(v_handle_894_, v_a_897_, lean_box(0));
return v___x_898_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___redArg___boxed(lean_object* v_x_899_, lean_object* v_handle_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_instMonadExceptOfEIO___aux__3___redArg(v_x_899_, v_handle_900_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3(lean_object* v_00_u03b5_903_, lean_object* v_00_u03b1_904_, lean_object* v_x_905_, lean_object* v_handle_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_apply_1(v_x_905_, lean_box(0));
if (lean_obj_tag(v___x_908_) == 0)
{
lean_dec_ref(v_handle_906_);
return v___x_908_;
}
else
{
lean_object* v_a_909_; lean_object* v___x_910_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref(v___x_908_);
v___x_910_ = lean_apply_2(v_handle_906_, v_a_909_, lean_box(0));
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___boxed(lean_object* v_00_u03b5_911_, lean_object* v_00_u03b1_912_, lean_object* v_x_913_, lean_object* v_handle_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_instMonadExceptOfEIO___aux__3(v_00_u03b5_911_, v_00_u03b1_912_, v_x_913_, v_handle_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object* v_00_u03b5_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = ((lean_object*)(l_instMonadExceptOfEIO___closed__2));
return v___x_923_;
}
}
static lean_object* _init_l_instOrElseEIO___closed__0(void){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_924_;
}
}
static lean_object* _init_l_instOrElseEIO___closed__1(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_obj_once(&l_instOrElseEIO___closed__0, &l_instOrElseEIO___closed__0_once, _init_l_instOrElseEIO___closed__0);
v___x_926_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_925_);
return v___x_926_;
}
}
static lean_object* _init_l_instOrElseEIO___closed__2(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_obj_once(&l_instOrElseEIO___closed__1, &l_instOrElseEIO___closed__1_once, _init_l_instOrElseEIO___closed__1);
v___x_928_ = lean_alloc_closure((void*)(l_MonadExcept_orElse), 6, 4);
lean_closure_set(v___x_928_, 0, lean_box(0));
lean_closure_set(v___x_928_, 1, lean_box(0));
lean_closure_set(v___x_928_, 2, v___x_927_);
lean_closure_set(v___x_928_, 3, lean_box(0));
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_instOrElseEIO(lean_object* v_00_u03b5_929_, lean_object* v_00_u03b1_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = lean_obj_once(&l_instOrElseEIO___closed__2, &l_instOrElseEIO___closed__2_once, _init_l_instOrElseEIO___closed__2);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1___redArg(lean_object* v_inst_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_934_, 0, v_inst_932_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1___redArg___boxed(lean_object* v_inst_935_, lean_object* v_s_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_instInhabitedEIO___aux__1___redArg(v_inst_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1(lean_object* v_00_u03b5_938_, lean_object* v_00_u03b1_939_, lean_object* v_inst_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v_inst_940_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object* v_00_u03b5_943_, lean_object* v_00_u03b1_944_, lean_object* v_inst_945_, lean_object* v_s_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_instInhabitedEIO___aux__1(v_00_u03b5_943_, v_00_u03b1_944_, v_inst_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___redArg(lean_object* v_inst_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_949_, 0, lean_box(0));
lean_closure_set(v___x_949_, 1, lean_box(0));
lean_closure_set(v___x_949_, 2, v_inst_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object* v_00_u03b5_950_, lean_object* v_00_u03b1_951_, lean_object* v_inst_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_953_, 0, lean_box(0));
lean_closure_set(v___x_953_, 1, lean_box(0));
lean_closure_set(v___x_953_, 2, v_inst_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_EIO_map___redArg(lean_object* v_f_954_, lean_object* v_x_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = lean_apply_1(v_x_955_, lean_box(0));
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_966_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_966_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = lean_apply_1(v_f_954_, v_a_958_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_f_954_);
v_a_967_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_957_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_957_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_map___redArg___boxed(lean_object* v_f_975_, lean_object* v_x_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_EIO_map___redArg(v_f_975_, v_x_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_EIO_map(lean_object* v_00_u03b1_979_, lean_object* v_00_u03b2_980_, lean_object* v_00_u03b5_981_, lean_object* v_f_982_, lean_object* v_x_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = lean_apply_1(v_x_983_, lean_box(0));
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_994_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_994_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = lean_apply_1(v_f_982_, v_a_986_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_990_);
v___x_992_ = v___x_988_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_f_982_);
v_a_995_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_985_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_985_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_map___boxed(lean_object* v_00_u03b1_1003_, lean_object* v_00_u03b2_1004_, lean_object* v_00_u03b5_1005_, lean_object* v_f_1006_, lean_object* v_x_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_EIO_map(v_00_u03b1_1003_, v_00_u03b2_1004_, v_00_u03b5_1005_, v_f_1006_, v_x_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_EIO_throw___redArg(lean_object* v_e_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_e_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_EIO_throw___redArg___boxed(lean_object* v_e_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_EIO_throw___redArg(v_e_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_EIO_throw(lean_object* v_00_u03b5_1016_, lean_object* v_00_u03b1_1017_, lean_object* v_e_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_e_1018_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_EIO_throw___boxed(lean_object* v_00_u03b5_1021_, lean_object* v_00_u03b1_1022_, lean_object* v_e_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_EIO_throw(v_00_u03b5_1021_, v_00_u03b1_1022_, v_e_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg(lean_object* v_x_1026_, lean_object* v_handle_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_apply_1(v_x_1026_, lean_box(0));
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_dec_ref(v_handle_1027_);
return v___x_1029_;
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref(v___x_1029_);
v___x_1031_ = lean_apply_2(v_handle_1027_, v_a_1030_, lean_box(0));
return v___x_1031_;
}
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg___boxed(lean_object* v_x_1032_, lean_object* v_handle_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_EIO_tryCatch___redArg(v_x_1032_, v_handle_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch(lean_object* v_00_u03b5_1036_, lean_object* v_00_u03b1_1037_, lean_object* v_x_1038_, lean_object* v_handle_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_apply_1(v_x_1038_, lean_box(0));
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_dec_ref(v_handle_1039_);
return v___x_1041_;
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1043_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref(v___x_1041_);
v___x_1043_ = lean_apply_2(v_handle_1039_, v_a_1042_, lean_box(0));
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___boxed(lean_object* v_00_u03b5_1044_, lean_object* v_00_u03b1_1045_, lean_object* v_x_1046_, lean_object* v_handle_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_EIO_tryCatch(v_00_u03b5_1044_, v_00_u03b1_1045_, v_x_1046_, v_handle_1047_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg(lean_object* v_e_1050_){
_start:
{
if (lean_obj_tag(v_e_1050_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_a_1052_ = lean_ctor_get(v_e_1050_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_e_1050_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v_e_1050_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v_e_1050_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 1);
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1060_ = lean_ctor_get(v_e_1050_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_e_1050_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v_e_1050_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v_e_1050_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 0);
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg___boxed(lean_object* v_e_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_EIO_ofExcept___redArg(v_e_1068_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept(lean_object* v_00_u03b5_1071_, lean_object* v_00_u03b1_1072_, lean_object* v_e_1073_){
_start:
{
if (lean_obj_tag(v_e_1073_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v_e_1073_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_e_1073_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v_e_1073_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v_e_1073_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 1);
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_a_1083_ = lean_ctor_get(v_e_1073_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_e_1073_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v_e_1073_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v_e_1073_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 0);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___boxed(lean_object* v_00_u03b5_1091_, lean_object* v_00_u03b1_1092_, lean_object* v_e_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_EIO_ofExcept(v_00_u03b5_1091_, v_00_u03b1_1092_, v_e_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_EIO_adapt___redArg(lean_object* v_f_1096_, lean_object* v_m_1097_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_apply_1(v_m_1097_, lean_box(0));
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_f_1096_);
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1116_; 
v_a_1108_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1110_ = v___x_1099_;
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1099_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1112_ = lean_apply_1(v_f_1096_, v_a_1108_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1112_);
v___x_1114_ = v___x_1110_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adapt___redArg___boxed(lean_object* v_f_1117_, lean_object* v_m_1118_, lean_object* v_s_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_EIO_adapt___redArg(v_f_1117_, v_m_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_EIO_adapt(lean_object* v_00_u03b5_1121_, lean_object* v_00_u03b5_x27_1122_, lean_object* v_00_u03b1_1123_, lean_object* v_f_1124_, lean_object* v_m_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_apply_1(v_m_1125_, lean_box(0));
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v_f_1124_);
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1144_; 
v_a_1136_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1138_ = v___x_1127_;
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1127_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = lean_apply_1(v_f_1124_, v_a_1136_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adapt___boxed(lean_object* v_00_u03b5_1145_, lean_object* v_00_u03b5_x27_1146_, lean_object* v_00_u03b1_1147_, lean_object* v_f_1148_, lean_object* v_m_1149_, lean_object* v_s_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_EIO_adapt(v_00_u03b5_1145_, v_00_u03b5_x27_1146_, v_00_u03b1_1147_, v_f_1148_, v_m_1149_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg(lean_object* v_f_1152_, lean_object* v_m_1153_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_apply_1(v_m_1153_, lean_box(0));
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_f_1152_);
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1172_; 
v_a_1164_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1166_ = v___x_1155_;
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1155_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1168_ = lean_apply_1(v_f_1152_, v_a_1164_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1168_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg___boxed(lean_object* v_f_1173_, lean_object* v_m_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_EIO_adaptExcept___redArg(v_f_1173_, v_m_1174_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept(lean_object* v_00_u03b5_1177_, lean_object* v_00_u03b5_x27_1178_, lean_object* v_00_u03b1_1179_, lean_object* v_f_1180_, lean_object* v_m_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_apply_1(v_m_1181_, lean_box(0));
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_f_1180_);
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1200_; 
v_a_1192_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1194_ = v___x_1183_;
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1183_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1196_ = lean_apply_1(v_f_1180_, v_a_1192_);
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
LEAN_EXPORT lean_object* l_EIO_adaptExcept___boxed(lean_object* v_00_u03b5_1201_, lean_object* v_00_u03b5_x27_1202_, lean_object* v_00_u03b1_1203_, lean_object* v_f_1204_, lean_object* v_m_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_EIO_adaptExcept(v_00_u03b5_1201_, v_00_u03b5_x27_1202_, v_00_u03b1_1203_, v_f_1204_, v_m_1205_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg(lean_object* v_act_1208_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_apply_1(v_act_1208_, lean_box(0));
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg___boxed(lean_object* v_act_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_BaseIO_toIO___redArg(v_act_1212_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO(lean_object* v_00_u03b1_1215_, lean_object* v_act_1216_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_apply_1(v_act_1216_, lean_box(0));
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___boxed(lean_object* v_00_u03b1_1220_, lean_object* v_act_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_BaseIO_toIO(v_00_u03b1_1220_, v_act_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___redArg(lean_object* v_f_1224_, lean_object* v_act_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_apply_1(v_act_1225_, lean_box(0));
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v_f_1224_);
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1244_; 
v_a_1236_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1238_ = v___x_1227_;
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1227_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1244_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1240_ = lean_apply_1(v_f_1224_, v_a_1236_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1240_);
v___x_1242_ = v___x_1238_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___redArg___boxed(lean_object* v_f_1245_, lean_object* v_act_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_EIO_toIO___redArg(v_f_1245_, v_act_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO(lean_object* v_00_u03b5_1249_, lean_object* v_00_u03b1_1250_, lean_object* v_f_1251_, lean_object* v_act_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_apply_1(v_act_1252_, lean_box(0));
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec_ref(v_f_1251_);
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1271_; 
v_a_1263_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1265_ = v___x_1254_;
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1254_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = lean_apply_1(v_f_1251_, v_a_1263_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1267_);
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___boxed(lean_object* v_00_u03b5_1272_, lean_object* v_00_u03b1_1273_, lean_object* v_f_1274_, lean_object* v_act_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_EIO_toIO(v_00_u03b5_1272_, v_00_u03b1_1273_, v_f_1274_, v_act_1275_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg(lean_object* v_act_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_apply_1(v_act_1278_, lean_box(0));
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1289_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1289_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_a_1281_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1285_);
v___x_1287_ = v___x_1283_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1298_; 
v_a_1290_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1292_ = v___x_1280_;
v_isShared_1293_ = v_isSharedCheck_1298_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1280_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1298_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v_a_1290_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set_tag(v___x_1292_, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1294_);
v___x_1296_ = v___x_1292_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg___boxed(lean_object* v_act_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_EIO_toIO_x27___redArg(v_act_1299_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27(lean_object* v_00_u03b5_1302_, lean_object* v_00_u03b1_1303_, lean_object* v_act_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_apply_1(v_act_1304_, lean_box(0));
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1315_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1311_, 0, v_a_1307_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1311_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
v_a_1316_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1318_ = v___x_1306_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1306_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_a_1316_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set_tag(v___x_1318_, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___boxed(lean_object* v_00_u03b5_1325_, lean_object* v_00_u03b1_1326_, lean_object* v_act_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_EIO_toIO_x27(v_00_u03b5_1325_, v_00_u03b1_1326_, v_act_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___redArg(lean_object* v_f_1330_, lean_object* v_act_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_apply_1(v_act_1331_, lean_box(0));
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_f_1330_);
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1350_; 
v_a_1342_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1344_ = v___x_1333_;
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1333_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_apply_1(v_f_1330_, v_a_1342_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1346_);
v___x_1348_ = v___x_1344_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___redArg___boxed(lean_object* v_f_1351_, lean_object* v_act_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_IO_toEIO___redArg(v_f_1351_, v_act_1352_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_IO_toEIO(lean_object* v_00_u03b5_1355_, lean_object* v_00_u03b1_1356_, lean_object* v_f_1357_, lean_object* v_act_1358_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_apply_1(v_act_1358_, lean_box(0));
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v_f_1357_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1377_; 
v_a_1369_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1371_ = v___x_1360_;
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1360_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = lean_apply_1(v_f_1357_, v_a_1369_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1373_);
v___x_1375_ = v___x_1371_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___boxed(lean_object* v_00_u03b5_1378_, lean_object* v_00_u03b1_1379_, lean_object* v_f_1380_, lean_object* v_act_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_IO_toEIO(v_00_u03b5_1378_, v_00_u03b1_1379_, v_f_1380_, v_act_1381_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO___redArg(lean_object* v_fn_1384_){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_box(0);
v___x_1386_ = lean_apply_1(v_fn_1384_, v___x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO(lean_object* v_00_u03b1_1387_, lean_object* v_fn_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_unsafeBaseIO___redArg(v_fn_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_unsafeEIO___redArg(lean_object* v_fn_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1391_, 0, lean_box(0));
lean_closure_set(v___x_1391_, 1, lean_box(0));
lean_closure_set(v___x_1391_, 2, v_fn_1390_);
v___x_1392_ = l_unsafeBaseIO___redArg(v___x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_unsafeEIO(lean_object* v_00_u03b5_1393_, lean_object* v_00_u03b1_1394_, lean_object* v_fn_1395_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1396_, 0, lean_box(0));
lean_closure_set(v___x_1396_, 1, lean_box(0));
lean_closure_set(v___x_1396_, 2, v_fn_1395_);
v___x_1397_ = l_unsafeBaseIO___redArg(v___x_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_unsafeIO___redArg(lean_object* v_fn_1398_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1399_, 0, lean_box(0));
lean_closure_set(v___x_1399_, 1, lean_box(0));
lean_closure_set(v___x_1399_, 2, v_fn_1398_);
v___x_1400_ = l_unsafeBaseIO___redArg(v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_unsafeIO(lean_object* v_00_u03b1_1401_, lean_object* v_fn_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1403_, 0, lean_box(0));
lean_closure_set(v___x_1403_, 1, lean_box(0));
lean_closure_set(v___x_1403_, 2, v_fn_1402_);
v___x_1404_ = l_unsafeBaseIO___redArg(v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_timeit___boxed(lean_object* v_00_u03b1_1409_, lean_object* v_msg_1410_, lean_object* v_fn_1411_, lean_object* v_a_00___x40___internal___hyg_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = lean_io_timeit(v_msg_1410_, v_fn_1411_);
lean_dec_ref(v_msg_1410_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_allocprof___boxed(lean_object* v_00_u03b1_1418_, lean_object* v_msg_1419_, lean_object* v_fn_1420_, lean_object* v_a_00___x40___internal___hyg_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = lean_io_allocprof(v_msg_1419_, v_fn_1420_);
lean_dec_ref(v_msg_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_IO_initializing___boxed(lean_object* v_a_00___x40___internal___hyg_1424_){
_start:
{
uint8_t v_res_1425_; lean_object* v_r_1426_; 
v_res_1425_ = lean_io_initializing();
v_r_1426_ = lean_box(v_res_1425_);
return v_r_1426_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_asTask___boxed(lean_object* v_00_u03b1_1431_, lean_object* v_act_1432_, lean_object* v_prio_1433_, lean_object* v_a_00___x40___internal___hyg_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = lean_io_as_task(v_act_1432_, v_prio_1433_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object* v_00_u03b1_1443_, lean_object* v_00_u03b2_1444_, lean_object* v_f_1445_, lean_object* v_t_1446_, lean_object* v_prio_1447_, lean_object* v_sync_1448_, lean_object* v_a_00___x40___internal___hyg_1449_){
_start:
{
uint8_t v_sync_boxed_1450_; lean_object* v_res_1451_; 
v_sync_boxed_1450_ = lean_unbox(v_sync_1448_);
v_res_1451_ = lean_io_map_task(v_f_1445_, v_t_1446_, v_prio_1447_, v_sync_boxed_1450_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object* v_00_u03b1_1459_, lean_object* v_00_u03b2_1460_, lean_object* v_t_1461_, lean_object* v_f_1462_, lean_object* v_prio_1463_, lean_object* v_sync_1464_, lean_object* v_a_00___x40___internal___hyg_1465_){
_start:
{
uint8_t v_sync_boxed_1466_; lean_object* v_res_1467_; 
v_sync_boxed_1466_ = lean_unbox(v_sync_1464_);
v_res_1467_ = lean_io_bind_task(v_t_1461_, v_f_1462_, v_prio_1463_, v_sync_boxed_1466_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg(lean_object* v_t_1468_, lean_object* v_f_1469_, lean_object* v_prio_1470_, uint8_t v_sync_1471_){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = lean_io_map_task(v_f_1469_, v_t_1468_, v_prio_1470_, v_sync_1471_);
lean_dec_ref(v___x_1473_);
v___x_1474_ = lean_box(0);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg___boxed(lean_object* v_t_1475_, lean_object* v_f_1476_, lean_object* v_prio_1477_, lean_object* v_sync_1478_, lean_object* v_a_1479_){
_start:
{
uint8_t v_sync_boxed_1480_; lean_object* v_res_1481_; 
v_sync_boxed_1480_ = lean_unbox(v_sync_1478_);
v_res_1481_ = l_BaseIO_chainTask___redArg(v_t_1475_, v_f_1476_, v_prio_1477_, v_sync_boxed_1480_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask(lean_object* v_00_u03b1_1482_, lean_object* v_t_1483_, lean_object* v_f_1484_, lean_object* v_prio_1485_, uint8_t v_sync_1486_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_BaseIO_chainTask___redArg(v_t_1483_, v_f_1484_, v_prio_1485_, v_sync_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___boxed(lean_object* v_00_u03b1_1489_, lean_object* v_t_1490_, lean_object* v_f_1491_, lean_object* v_prio_1492_, lean_object* v_sync_1493_, lean_object* v_a_1494_){
_start:
{
uint8_t v_sync_boxed_1495_; lean_object* v_res_1496_; 
v_sync_boxed_1495_ = lean_unbox(v_sync_1493_);
v_res_1496_ = l_BaseIO_chainTask(v_00_u03b1_1489_, v_t_1490_, v_f_1491_, v_prio_1492_, v_sync_boxed_1495_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(lean_object* v_x_1497_, lean_object* v_f_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1501_, 0, v_a_1499_);
lean_ctor_set(v___x_1501_, 1, v_x_1497_);
v___x_1502_ = l_List_reverse___redArg(v___x_1501_);
v___x_1503_ = lean_apply_2(v_f_1498_, v___x_1502_, lean_box(0));
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed(lean_object* v_x_1504_, lean_object* v_f_1505_, lean_object* v_a_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(v_x_1504_, v_f_1505_, v_a_1506_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed(lean_object* v_x_1509_, lean_object* v_f_1510_, lean_object* v_prio_1511_, lean_object* v_sync_1512_, lean_object* v_tail_1513_, lean_object* v_a_1514_, lean_object* v___y_1515_){
_start:
{
uint8_t v_sync_boxed_1516_; lean_object* v_res_1517_; 
v_sync_boxed_1516_ = lean_unbox(v_sync_1512_);
v_res_1517_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(v_x_1509_, v_f_1510_, v_prio_1511_, v_sync_boxed_1516_, v_tail_1513_, v_a_1514_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(lean_object* v_f_1518_, lean_object* v_prio_1519_, uint8_t v_sync_1520_, lean_object* v_x_1521_, lean_object* v_x_1522_){
_start:
{
if (lean_obj_tag(v_x_1521_) == 0)
{
if (v_sync_1520_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = l_List_reverse___redArg(v_x_1522_);
v___x_1525_ = lean_apply_1(v_f_1518_, v___x_1524_);
v___x_1526_ = lean_io_as_task(v___x_1525_, v_prio_1519_);
return v___x_1526_;
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v_prio_1519_);
v___x_1527_ = l_List_reverse___redArg(v_x_1522_);
v___x_1528_ = lean_apply_2(v_f_1518_, v___x_1527_, lean_box(0));
v___x_1529_ = lean_task_pure(v___x_1528_);
return v___x_1529_;
}
}
else
{
lean_object* v_tail_1530_; 
v_tail_1530_ = lean_ctor_get(v_x_1521_, 1);
if (lean_obj_tag(v_tail_1530_) == 0)
{
lean_object* v_head_1531_; lean_object* v___f_1532_; lean_object* v___x_1533_; 
v_head_1531_ = lean_ctor_get(v_x_1521_, 0);
lean_inc(v_head_1531_);
lean_dec_ref(v_x_1521_);
v___f_1532_ = lean_alloc_closure((void*)(l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1532_, 0, v_x_1522_);
lean_closure_set(v___f_1532_, 1, v_f_1518_);
v___x_1533_ = lean_io_map_task(v___f_1532_, v_head_1531_, v_prio_1519_, v_sync_1520_);
return v___x_1533_;
}
else
{
lean_object* v_head_1534_; lean_object* v___x_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; 
lean_inc(v_tail_1530_);
v_head_1534_ = lean_ctor_get(v_x_1521_, 0);
lean_inc(v_head_1534_);
lean_dec_ref(v_x_1521_);
v___x_1535_ = lean_box(v_sync_1520_);
lean_inc(v_prio_1519_);
v___f_1536_ = lean_alloc_closure((void*)(l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1536_, 0, v_x_1522_);
lean_closure_set(v___f_1536_, 1, v_f_1518_);
lean_closure_set(v___f_1536_, 2, v_prio_1519_);
lean_closure_set(v___f_1536_, 3, v___x_1535_);
lean_closure_set(v___f_1536_, 4, v_tail_1530_);
v___x_1537_ = lean_io_bind_task(v_head_1534_, v___f_1536_, v_prio_1519_, v_sync_1520_);
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(lean_object* v_x_1538_, lean_object* v_f_1539_, lean_object* v_prio_1540_, uint8_t v_sync_1541_, lean_object* v_tail_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_a_1543_);
lean_ctor_set(v___x_1545_, 1, v_x_1538_);
v___x_1546_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_1539_, v_prio_1540_, v_sync_1541_, v_tail_1542_, v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___boxed(lean_object* v_f_1547_, lean_object* v_prio_1548_, lean_object* v_sync_1549_, lean_object* v_x_1550_, lean_object* v_x_1551_, lean_object* v_a_1552_){
_start:
{
uint8_t v_sync_boxed_1553_; lean_object* v_res_1554_; 
v_sync_boxed_1553_ = lean_unbox(v_sync_1549_);
v_res_1554_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_1547_, v_prio_1548_, v_sync_boxed_1553_, v_x_1550_, v_x_1551_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go(lean_object* v_00_u03b1_1555_, lean_object* v_00_u03b2_1556_, lean_object* v_f_1557_, lean_object* v_prio_1558_, uint8_t v_sync_1559_, lean_object* v_x_1560_, lean_object* v_x_1561_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_1557_, v_prio_1558_, v_sync_1559_, v_x_1560_, v_x_1561_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___boxed(lean_object* v_00_u03b1_1564_, lean_object* v_00_u03b2_1565_, lean_object* v_f_1566_, lean_object* v_prio_1567_, lean_object* v_sync_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_, lean_object* v_a_1571_){
_start:
{
uint8_t v_sync_boxed_1572_; lean_object* v_res_1573_; 
v_sync_boxed_1572_ = lean_unbox(v_sync_1568_);
v_res_1573_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go(v_00_u03b1_1564_, v_00_u03b2_1565_, v_f_1566_, v_prio_1567_, v_sync_boxed_1572_, v_x_1569_, v_x_1570_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg(lean_object* v_f_1574_, lean_object* v_tasks_1575_, lean_object* v_prio_1576_, uint8_t v_sync_1577_){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_box(0);
v___x_1580_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_1574_, v_prio_1576_, v_sync_1577_, v_tasks_1575_, v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg___boxed(lean_object* v_f_1581_, lean_object* v_tasks_1582_, lean_object* v_prio_1583_, lean_object* v_sync_1584_, lean_object* v_a_1585_){
_start:
{
uint8_t v_sync_boxed_1586_; lean_object* v_res_1587_; 
v_sync_boxed_1586_ = lean_unbox(v_sync_1584_);
v_res_1587_ = l_BaseIO_mapTasks___redArg(v_f_1581_, v_tasks_1582_, v_prio_1583_, v_sync_boxed_1586_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks(lean_object* v_00_u03b1_1588_, lean_object* v_00_u03b2_1589_, lean_object* v_f_1590_, lean_object* v_tasks_1591_, lean_object* v_prio_1592_, uint8_t v_sync_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_BaseIO_mapTasks___redArg(v_f_1590_, v_tasks_1591_, v_prio_1592_, v_sync_1593_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___boxed(lean_object* v_00_u03b1_1596_, lean_object* v_00_u03b2_1597_, lean_object* v_f_1598_, lean_object* v_tasks_1599_, lean_object* v_prio_1600_, lean_object* v_sync_1601_, lean_object* v_a_1602_){
_start:
{
uint8_t v_sync_boxed_1603_; lean_object* v_res_1604_; 
v_sync_boxed_1603_ = lean_unbox(v_sync_1601_);
v_res_1604_ = l_BaseIO_mapTasks(v_00_u03b1_1596_, v_00_u03b2_1597_, v_f_1598_, v_tasks_1599_, v_prio_1600_, v_sync_boxed_1603_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___redArg(lean_object* v_act_1605_, lean_object* v_prio_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1608_, 0, lean_box(0));
lean_closure_set(v___x_1608_, 1, lean_box(0));
lean_closure_set(v___x_1608_, 2, v_act_1605_);
v___x_1609_ = lean_io_as_task(v___x_1608_, v_prio_1606_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___redArg___boxed(lean_object* v_act_1610_, lean_object* v_prio_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_EIO_asTask___redArg(v_act_1610_, v_prio_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask(lean_object* v_00_u03b5_1614_, lean_object* v_00_u03b1_1615_, lean_object* v_act_1616_, lean_object* v_prio_1617_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1619_, 0, lean_box(0));
lean_closure_set(v___x_1619_, 1, lean_box(0));
lean_closure_set(v___x_1619_, 2, v_act_1616_);
v___x_1620_ = lean_io_as_task(v___x_1619_, v_prio_1617_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___boxed(lean_object* v_00_u03b5_1621_, lean_object* v_00_u03b1_1622_, lean_object* v_act_1623_, lean_object* v_prio_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_EIO_asTask(v_00_u03b5_1621_, v_00_u03b1_1622_, v_act_1623_, v_prio_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0(lean_object* v_f_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_apply_2(v_f_1627_, v_a_1628_, lean_box(0));
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set_tag(v___x_1633_, 1);
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
v_a_1639_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1630_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1630_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 0);
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0___boxed(lean_object* v_f_1647_, lean_object* v_a_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_EIO_mapTask___redArg___lam__0(v_f_1647_, v_a_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg(lean_object* v_f_1651_, lean_object* v_t_1652_, lean_object* v_prio_1653_, uint8_t v_sync_1654_){
_start:
{
lean_object* v___f_1656_; lean_object* v___x_1657_; 
v___f_1656_ = lean_alloc_closure((void*)(l_EIO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1656_, 0, v_f_1651_);
v___x_1657_ = lean_io_map_task(v___f_1656_, v_t_1652_, v_prio_1653_, v_sync_1654_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___boxed(lean_object* v_f_1658_, lean_object* v_t_1659_, lean_object* v_prio_1660_, lean_object* v_sync_1661_, lean_object* v_a_1662_){
_start:
{
uint8_t v_sync_boxed_1663_; lean_object* v_res_1664_; 
v_sync_boxed_1663_ = lean_unbox(v_sync_1661_);
v_res_1664_ = l_EIO_mapTask___redArg(v_f_1658_, v_t_1659_, v_prio_1660_, v_sync_boxed_1663_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask(lean_object* v_00_u03b1_1665_, lean_object* v_00_u03b5_1666_, lean_object* v_00_u03b2_1667_, lean_object* v_f_1668_, lean_object* v_t_1669_, lean_object* v_prio_1670_, uint8_t v_sync_1671_){
_start:
{
lean_object* v___f_1673_; lean_object* v___x_1674_; 
v___f_1673_ = lean_alloc_closure((void*)(l_EIO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1673_, 0, v_f_1668_);
v___x_1674_ = lean_io_map_task(v___f_1673_, v_t_1669_, v_prio_1670_, v_sync_1671_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___boxed(lean_object* v_00_u03b1_1675_, lean_object* v_00_u03b5_1676_, lean_object* v_00_u03b2_1677_, lean_object* v_f_1678_, lean_object* v_t_1679_, lean_object* v_prio_1680_, lean_object* v_sync_1681_, lean_object* v_a_1682_){
_start:
{
uint8_t v_sync_boxed_1683_; lean_object* v_res_1684_; 
v_sync_boxed_1683_ = lean_unbox(v_sync_1681_);
v_res_1684_ = l_EIO_mapTask(v_00_u03b1_1675_, v_00_u03b5_1676_, v_00_u03b2_1677_, v_f_1678_, v_t_1679_, v_prio_1680_, v_sync_boxed_1683_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0(lean_object* v_f_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_apply_2(v_f_1685_, v_a_1686_, lean_box(0));
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref(v___x_1688_);
return v_a_1689_;
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1698_; 
v_a_1690_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1692_ = v___x_1688_;
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1688_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set_tag(v___x_1692_, 0);
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_task_pure(v___x_1695_);
return v___x_1696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0___boxed(lean_object* v_f_1699_, lean_object* v_a_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_EIO_bindTask___redArg___lam__0(v_f_1699_, v_a_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg(lean_object* v_t_1703_, lean_object* v_f_1704_, lean_object* v_prio_1705_, uint8_t v_sync_1706_){
_start:
{
lean_object* v___f_1708_; lean_object* v___x_1709_; 
v___f_1708_ = lean_alloc_closure((void*)(l_EIO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1708_, 0, v_f_1704_);
v___x_1709_ = lean_io_bind_task(v_t_1703_, v___f_1708_, v_prio_1705_, v_sync_1706_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___boxed(lean_object* v_t_1710_, lean_object* v_f_1711_, lean_object* v_prio_1712_, lean_object* v_sync_1713_, lean_object* v_a_1714_){
_start:
{
uint8_t v_sync_boxed_1715_; lean_object* v_res_1716_; 
v_sync_boxed_1715_ = lean_unbox(v_sync_1713_);
v_res_1716_ = l_EIO_bindTask___redArg(v_t_1710_, v_f_1711_, v_prio_1712_, v_sync_boxed_1715_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask(lean_object* v_00_u03b1_1717_, lean_object* v_00_u03b5_1718_, lean_object* v_00_u03b2_1719_, lean_object* v_t_1720_, lean_object* v_f_1721_, lean_object* v_prio_1722_, uint8_t v_sync_1723_){
_start:
{
lean_object* v___f_1725_; lean_object* v___x_1726_; 
v___f_1725_ = lean_alloc_closure((void*)(l_EIO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1725_, 0, v_f_1721_);
v___x_1726_ = lean_io_bind_task(v_t_1720_, v___f_1725_, v_prio_1722_, v_sync_1723_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___boxed(lean_object* v_00_u03b1_1727_, lean_object* v_00_u03b5_1728_, lean_object* v_00_u03b2_1729_, lean_object* v_t_1730_, lean_object* v_f_1731_, lean_object* v_prio_1732_, lean_object* v_sync_1733_, lean_object* v_a_1734_){
_start:
{
uint8_t v_sync_boxed_1735_; lean_object* v_res_1736_; 
v_sync_boxed_1735_ = lean_unbox(v_sync_1733_);
v_res_1736_ = l_EIO_bindTask(v_00_u03b1_1727_, v_00_u03b5_1728_, v_00_u03b2_1729_, v_t_1730_, v_f_1731_, v_prio_1732_, v_sync_boxed_1735_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0(lean_object* v_f_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_apply_2(v_f_1737_, v_a_1738_, lean_box(0));
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set_tag(v___x_1743_, 1);
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
v_a_1749_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1740_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1740_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set_tag(v___x_1751_, 0);
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0___boxed(lean_object* v_f_1757_, lean_object* v_a_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_EIO_chainTask___redArg___lam__0(v_f_1757_, v_a_1758_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg(lean_object* v_t_1761_, lean_object* v_f_1762_, lean_object* v_prio_1763_, uint8_t v_sync_1764_){
_start:
{
lean_object* v___f_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___f_1766_ = lean_alloc_closure((void*)(l_EIO_chainTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1766_, 0, v_f_1762_);
v___x_1767_ = lean_io_map_task(v___f_1766_, v_t_1761_, v_prio_1763_, v_sync_1764_);
lean_dec_ref(v___x_1767_);
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___boxed(lean_object* v_t_1770_, lean_object* v_f_1771_, lean_object* v_prio_1772_, lean_object* v_sync_1773_, lean_object* v_a_1774_){
_start:
{
uint8_t v_sync_boxed_1775_; lean_object* v_res_1776_; 
v_sync_boxed_1775_ = lean_unbox(v_sync_1773_);
v_res_1776_ = l_EIO_chainTask___redArg(v_t_1770_, v_f_1771_, v_prio_1772_, v_sync_boxed_1775_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask(lean_object* v_00_u03b1_1777_, lean_object* v_00_u03b5_1778_, lean_object* v_t_1779_, lean_object* v_f_1780_, lean_object* v_prio_1781_, uint8_t v_sync_1782_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_EIO_chainTask___redArg(v_t_1779_, v_f_1780_, v_prio_1781_, v_sync_1782_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___boxed(lean_object* v_00_u03b1_1785_, lean_object* v_00_u03b5_1786_, lean_object* v_t_1787_, lean_object* v_f_1788_, lean_object* v_prio_1789_, lean_object* v_sync_1790_, lean_object* v_a_1791_){
_start:
{
uint8_t v_sync_boxed_1792_; lean_object* v_res_1793_; 
v_sync_boxed_1792_ = lean_unbox(v_sync_1790_);
v_res_1793_ = l_EIO_chainTask(v_00_u03b1_1785_, v_00_u03b5_1786_, v_t_1787_, v_f_1788_, v_prio_1789_, v_sync_boxed_1792_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0(lean_object* v_f_1794_, lean_object* v_as_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_apply_2(v_f_1794_, v_as_1795_, lean_box(0));
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set_tag(v___x_1800_, 1);
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
v_a_1806_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1797_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1797_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set_tag(v___x_1808_, 0);
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0___boxed(lean_object* v_f_1814_, lean_object* v_as_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_EIO_mapTasks___redArg___lam__0(v_f_1814_, v_as_1815_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg(lean_object* v_f_1818_, lean_object* v_tasks_1819_, lean_object* v_prio_1820_, uint8_t v_sync_1821_){
_start:
{
lean_object* v___f_1823_; lean_object* v___x_1824_; 
v___f_1823_ = lean_alloc_closure((void*)(l_EIO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1823_, 0, v_f_1818_);
v___x_1824_ = l_BaseIO_mapTasks___redArg(v___f_1823_, v_tasks_1819_, v_prio_1820_, v_sync_1821_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___boxed(lean_object* v_f_1825_, lean_object* v_tasks_1826_, lean_object* v_prio_1827_, lean_object* v_sync_1828_, lean_object* v_a_1829_){
_start:
{
uint8_t v_sync_boxed_1830_; lean_object* v_res_1831_; 
v_sync_boxed_1830_ = lean_unbox(v_sync_1828_);
v_res_1831_ = l_EIO_mapTasks___redArg(v_f_1825_, v_tasks_1826_, v_prio_1827_, v_sync_boxed_1830_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks(lean_object* v_00_u03b1_1832_, lean_object* v_00_u03b5_1833_, lean_object* v_00_u03b2_1834_, lean_object* v_f_1835_, lean_object* v_tasks_1836_, lean_object* v_prio_1837_, uint8_t v_sync_1838_){
_start:
{
lean_object* v___f_1840_; lean_object* v___x_1841_; 
v___f_1840_ = lean_alloc_closure((void*)(l_EIO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1840_, 0, v_f_1835_);
v___x_1841_ = l_BaseIO_mapTasks___redArg(v___f_1840_, v_tasks_1836_, v_prio_1837_, v_sync_1838_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___boxed(lean_object* v_00_u03b1_1842_, lean_object* v_00_u03b5_1843_, lean_object* v_00_u03b2_1844_, lean_object* v_f_1845_, lean_object* v_tasks_1846_, lean_object* v_prio_1847_, lean_object* v_sync_1848_, lean_object* v_a_1849_){
_start:
{
uint8_t v_sync_boxed_1850_; lean_object* v_res_1851_; 
v_sync_boxed_1850_ = lean_unbox(v_sync_1848_);
v_res_1851_ = l_EIO_mapTasks(v_00_u03b1_1842_, v_00_u03b5_1843_, v_00_u03b2_1844_, v_f_1845_, v_tasks_1846_, v_prio_1847_, v_sync_boxed_1850_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg(lean_object* v_inst_1852_, lean_object* v_e_1853_){
_start:
{
if (lean_obj_tag(v_e_1853_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1864_; 
v_a_1855_ = lean_ctor_get(v_e_1853_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_e_1853_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1857_ = v_e_1853_;
v_isShared_1858_ = v_isSharedCheck_1864_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v_e_1853_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1864_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1859_ = lean_apply_1(v_inst_1852_, v_a_1855_);
v___x_1860_ = lean_mk_io_user_error(v___x_1859_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set_tag(v___x_1857_, 1);
lean_ctor_set(v___x_1857_, 0, v___x_1860_);
v___x_1862_ = v___x_1857_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec_ref(v_inst_1852_);
v_a_1865_ = lean_ctor_get(v_e_1853_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_e_1853_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v_e_1853_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v_e_1853_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set_tag(v___x_1867_, 0);
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg___boxed(lean_object* v_inst_1873_, lean_object* v_e_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_IO_ofExcept___redArg(v_inst_1873_, v_e_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept(lean_object* v_00_u03b5_1877_, lean_object* v_00_u03b1_1878_, lean_object* v_inst_1879_, lean_object* v_e_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_IO_ofExcept___redArg(v_inst_1879_, v_e_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___boxed(lean_object* v_00_u03b5_1883_, lean_object* v_00_u03b1_1884_, lean_object* v_inst_1885_, lean_object* v_e_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_IO_ofExcept(v_00_u03b5_1883_, v_00_u03b1_1884_, v_inst_1885_, v_e_1886_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg(lean_object* v_fn_1889_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = lean_box(0);
v___x_1892_ = lean_apply_1(v_fn_1889_, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg___boxed(lean_object* v_fn_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_IO_lazyPure___redArg(v_fn_1894_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure(lean_object* v_00_u03b1_1897_, lean_object* v_fn_1898_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_IO_lazyPure___redArg(v_fn_1898_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___boxed(lean_object* v_00_u03b1_1901_, lean_object* v_fn_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_IO_lazyPure(v_00_u03b1_1901_, v_fn_1902_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_IO_monoMsNow___boxed(lean_object* v_a_00___x40___internal___hyg_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = lean_io_mono_ms_now();
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_IO_monoNanosNow___boxed(lean_object* v_a_00___x40___internal___hyg_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = lean_io_mono_nanos_now();
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_IO_getRandomBytes___boxed(lean_object* v_nBytes_1913_, lean_object* v_a_00___x40___internal___hyg_1914_){
_start:
{
size_t v_nBytes_boxed_1915_; lean_object* v_res_1916_; 
v_nBytes_boxed_1915_ = lean_unbox_usize(v_nBytes_1913_);
lean_dec(v_nBytes_1913_);
v_res_1916_ = lean_io_get_random_bytes(v_nBytes_boxed_1915_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___lam__0(lean_object* v_x_1918_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_box(0);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___lam__0___boxed(lean_object* v_s_1920_, lean_object* v_x_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_IO_sleep___lam__0(v_x_1921_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_IO_sleep(uint32_t v_ms_1923_){
_start:
{
lean_object* v___f_1925_; lean_object* v___x_1926_; 
v___f_1925_ = lean_alloc_closure((void*)(l_IO_sleep___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1925_, 0, lean_box(0));
v___x_1926_ = lean_dbg_sleep(v_ms_1923_, v___f_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___boxed(lean_object* v_ms_1927_, lean_object* v_s_1928_){
_start:
{
uint32_t v_ms_boxed_1929_; lean_object* v_res_1930_; 
v_ms_boxed_1929_ = lean_unbox_uint32(v_ms_1927_);
lean_dec(v_ms_1927_);
v_res_1930_ = l_IO_sleep(v_ms_boxed_1929_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___redArg(lean_object* v_act_1931_, lean_object* v_prio_1932_){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1934_, 0, lean_box(0));
lean_closure_set(v___x_1934_, 1, lean_box(0));
lean_closure_set(v___x_1934_, 2, v_act_1931_);
v___x_1935_ = lean_io_as_task(v___x_1934_, v_prio_1932_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___redArg___boxed(lean_object* v_act_1936_, lean_object* v_prio_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_IO_asTask___redArg(v_act_1936_, v_prio_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_IO_asTask(lean_object* v_00_u03b1_1940_, lean_object* v_act_1941_, lean_object* v_prio_1942_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1944_, 0, lean_box(0));
lean_closure_set(v___x_1944_, 1, lean_box(0));
lean_closure_set(v___x_1944_, 2, v_act_1941_);
v___x_1945_ = lean_io_as_task(v___x_1944_, v_prio_1942_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_act_1947_, lean_object* v_prio_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_IO_asTask(v_00_u03b1_1946_, v_act_1947_, v_prio_1948_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0(lean_object* v_f_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_apply_2(v_f_1951_, v_a_1952_, lean_box(0));
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set_tag(v___x_1957_, 1);
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
v_a_1963_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1954_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1954_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 0);
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0___boxed(lean_object* v_f_1971_, lean_object* v_a_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_IO_mapTask___redArg___lam__0(v_f_1971_, v_a_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg(lean_object* v_f_1975_, lean_object* v_t_1976_, lean_object* v_prio_1977_, uint8_t v_sync_1978_){
_start:
{
lean_object* v___f_1980_; lean_object* v___x_1981_; 
v___f_1980_ = lean_alloc_closure((void*)(l_IO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1980_, 0, v_f_1975_);
v___x_1981_ = lean_io_map_task(v___f_1980_, v_t_1976_, v_prio_1977_, v_sync_1978_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___boxed(lean_object* v_f_1982_, lean_object* v_t_1983_, lean_object* v_prio_1984_, lean_object* v_sync_1985_, lean_object* v_a_1986_){
_start:
{
uint8_t v_sync_boxed_1987_; lean_object* v_res_1988_; 
v_sync_boxed_1987_ = lean_unbox(v_sync_1985_);
v_res_1988_ = l_IO_mapTask___redArg(v_f_1982_, v_t_1983_, v_prio_1984_, v_sync_boxed_1987_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask(lean_object* v_00_u03b1_1989_, lean_object* v_00_u03b2_1990_, lean_object* v_f_1991_, lean_object* v_t_1992_, lean_object* v_prio_1993_, uint8_t v_sync_1994_){
_start:
{
lean_object* v___f_1996_; lean_object* v___x_1997_; 
v___f_1996_ = lean_alloc_closure((void*)(l_IO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1996_, 0, v_f_1991_);
v___x_1997_ = lean_io_map_task(v___f_1996_, v_t_1992_, v_prio_1993_, v_sync_1994_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___boxed(lean_object* v_00_u03b1_1998_, lean_object* v_00_u03b2_1999_, lean_object* v_f_2000_, lean_object* v_t_2001_, lean_object* v_prio_2002_, lean_object* v_sync_2003_, lean_object* v_a_2004_){
_start:
{
uint8_t v_sync_boxed_2005_; lean_object* v_res_2006_; 
v_sync_boxed_2005_ = lean_unbox(v_sync_2003_);
v_res_2006_ = l_IO_mapTask(v_00_u03b1_1998_, v_00_u03b2_1999_, v_f_2000_, v_t_2001_, v_prio_2002_, v_sync_boxed_2005_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0(lean_object* v_f_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_apply_2(v_f_2007_, v_a_2008_, lean_box(0));
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref(v___x_2010_);
return v_a_2011_;
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
v_a_2012_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2014_ = v___x_2010_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 0);
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_task_pure(v___x_2017_);
return v___x_2018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0___boxed(lean_object* v_f_2021_, lean_object* v_a_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_IO_bindTask___redArg___lam__0(v_f_2021_, v_a_2022_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg(lean_object* v_t_2025_, lean_object* v_f_2026_, lean_object* v_prio_2027_, uint8_t v_sync_2028_){
_start:
{
lean_object* v___f_2030_; lean_object* v___x_2031_; 
v___f_2030_ = lean_alloc_closure((void*)(l_IO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2030_, 0, v_f_2026_);
v___x_2031_ = lean_io_bind_task(v_t_2025_, v___f_2030_, v_prio_2027_, v_sync_2028_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___boxed(lean_object* v_t_2032_, lean_object* v_f_2033_, lean_object* v_prio_2034_, lean_object* v_sync_2035_, lean_object* v_a_2036_){
_start:
{
uint8_t v_sync_boxed_2037_; lean_object* v_res_2038_; 
v_sync_boxed_2037_ = lean_unbox(v_sync_2035_);
v_res_2038_ = l_IO_bindTask___redArg(v_t_2032_, v_f_2033_, v_prio_2034_, v_sync_boxed_2037_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask(lean_object* v_00_u03b1_2039_, lean_object* v_00_u03b2_2040_, lean_object* v_t_2041_, lean_object* v_f_2042_, lean_object* v_prio_2043_, uint8_t v_sync_2044_){
_start:
{
lean_object* v___f_2046_; lean_object* v___x_2047_; 
v___f_2046_ = lean_alloc_closure((void*)(l_IO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2046_, 0, v_f_2042_);
v___x_2047_ = lean_io_bind_task(v_t_2041_, v___f_2046_, v_prio_2043_, v_sync_2044_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___boxed(lean_object* v_00_u03b1_2048_, lean_object* v_00_u03b2_2049_, lean_object* v_t_2050_, lean_object* v_f_2051_, lean_object* v_prio_2052_, lean_object* v_sync_2053_, lean_object* v_a_2054_){
_start:
{
uint8_t v_sync_boxed_2055_; lean_object* v_res_2056_; 
v_sync_boxed_2055_ = lean_unbox(v_sync_2053_);
v_res_2056_ = l_IO_bindTask(v_00_u03b1_2048_, v_00_u03b2_2049_, v_t_2050_, v_f_2051_, v_prio_2052_, v_sync_boxed_2055_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___redArg(lean_object* v_t_2057_, lean_object* v_f_2058_, lean_object* v_prio_2059_, uint8_t v_sync_2060_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_EIO_chainTask___redArg(v_t_2057_, v_f_2058_, v_prio_2059_, v_sync_2060_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___redArg___boxed(lean_object* v_t_2063_, lean_object* v_f_2064_, lean_object* v_prio_2065_, lean_object* v_sync_2066_, lean_object* v_a_2067_){
_start:
{
uint8_t v_sync_boxed_2068_; lean_object* v_res_2069_; 
v_sync_boxed_2068_ = lean_unbox(v_sync_2066_);
v_res_2069_ = l_IO_chainTask___redArg(v_t_2063_, v_f_2064_, v_prio_2065_, v_sync_boxed_2068_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask(lean_object* v_00_u03b1_2070_, lean_object* v_t_2071_, lean_object* v_f_2072_, lean_object* v_prio_2073_, uint8_t v_sync_2074_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_EIO_chainTask___redArg(v_t_2071_, v_f_2072_, v_prio_2073_, v_sync_2074_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___boxed(lean_object* v_00_u03b1_2077_, lean_object* v_t_2078_, lean_object* v_f_2079_, lean_object* v_prio_2080_, lean_object* v_sync_2081_, lean_object* v_a_2082_){
_start:
{
uint8_t v_sync_boxed_2083_; lean_object* v_res_2084_; 
v_sync_boxed_2083_ = lean_unbox(v_sync_2081_);
v_res_2084_ = l_IO_chainTask(v_00_u03b1_2077_, v_t_2078_, v_f_2079_, v_prio_2080_, v_sync_boxed_2083_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0(lean_object* v_f_2085_, lean_object* v_as_2086_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_apply_2(v_f_2085_, v_as_2086_, lean_box(0));
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set_tag(v___x_2091_, 1);
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
v_a_2097_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2088_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2088_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set_tag(v___x_2099_, 0);
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0___boxed(lean_object* v_f_2105_, lean_object* v_as_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_IO_mapTasks___redArg___lam__0(v_f_2105_, v_as_2106_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg(lean_object* v_f_2109_, lean_object* v_tasks_2110_, lean_object* v_prio_2111_, uint8_t v_sync_2112_){
_start:
{
lean_object* v___f_2114_; lean_object* v___x_2115_; 
v___f_2114_ = lean_alloc_closure((void*)(l_IO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2114_, 0, v_f_2109_);
v___x_2115_ = l_BaseIO_mapTasks___redArg(v___f_2114_, v_tasks_2110_, v_prio_2111_, v_sync_2112_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___boxed(lean_object* v_f_2116_, lean_object* v_tasks_2117_, lean_object* v_prio_2118_, lean_object* v_sync_2119_, lean_object* v_a_2120_){
_start:
{
uint8_t v_sync_boxed_2121_; lean_object* v_res_2122_; 
v_sync_boxed_2121_ = lean_unbox(v_sync_2119_);
v_res_2122_ = l_IO_mapTasks___redArg(v_f_2116_, v_tasks_2117_, v_prio_2118_, v_sync_boxed_2121_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks(lean_object* v_00_u03b1_2123_, lean_object* v_00_u03b2_2124_, lean_object* v_f_2125_, lean_object* v_tasks_2126_, lean_object* v_prio_2127_, uint8_t v_sync_2128_){
_start:
{
lean_object* v___f_2130_; lean_object* v___x_2131_; 
v___f_2130_ = lean_alloc_closure((void*)(l_IO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2130_, 0, v_f_2125_);
v___x_2131_ = l_BaseIO_mapTasks___redArg(v___f_2130_, v_tasks_2126_, v_prio_2127_, v_sync_2128_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___boxed(lean_object* v_00_u03b1_2132_, lean_object* v_00_u03b2_2133_, lean_object* v_f_2134_, lean_object* v_tasks_2135_, lean_object* v_prio_2136_, lean_object* v_sync_2137_, lean_object* v_a_2138_){
_start:
{
uint8_t v_sync_boxed_2139_; lean_object* v_res_2140_; 
v_sync_boxed_2139_ = lean_unbox(v_sync_2137_);
v_res_2140_ = l_IO_mapTasks(v_00_u03b1_2132_, v_00_u03b2_2133_, v_f_2134_, v_tasks_2135_, v_prio_2136_, v_sync_boxed_2139_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_IO_checkCanceled___boxed(lean_object* v_a_00___x40___internal___hyg_2142_){
_start:
{
uint8_t v_res_2143_; lean_object* v_r_2144_; 
v_res_2143_ = lean_io_check_canceled();
v_r_2144_ = lean_box(v_res_2143_);
return v_r_2144_;
}
}
LEAN_EXPORT lean_object* l_IO_cancel___boxed(lean_object* v_00_u03b1_2148_, lean_object* v_a_00___x40___internal___hyg_2149_, lean_object* v_a_00___x40___internal___hyg_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = lean_io_cancel(v_a_00___x40___internal___hyg_2149_);
lean_dec_ref(v_a_00___x40___internal___hyg_2149_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx(uint8_t v_x_2152_){
_start:
{
switch(v_x_2152_)
{
case 0:
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_unsigned_to_nat(0u);
return v___x_2153_;
}
case 1:
{
lean_object* v___x_2154_; 
v___x_2154_ = lean_unsigned_to_nat(1u);
return v___x_2154_;
}
default: 
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_unsigned_to_nat(2u);
return v___x_2155_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx___boxed(lean_object* v_x_2156_){
_start:
{
uint8_t v_x_boxed_2157_; lean_object* v_res_2158_; 
v_x_boxed_2157_ = lean_unbox(v_x_2156_);
v_res_2158_ = l_IO_TaskState_ctorIdx(v_x_boxed_2157_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx(uint8_t v_x_2159_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_IO_TaskState_ctorIdx(v_x_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toCtorIdx___boxed(lean_object* v_x_2161_){
_start:
{
uint8_t v_x_4__boxed_2162_; lean_object* v_res_2163_; 
v_x_4__boxed_2162_ = lean_unbox(v_x_2161_);
v_res_2163_ = l_IO_TaskState_toCtorIdx(v_x_4__boxed_2162_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg(lean_object* v_k_2164_){
_start:
{
lean_inc(v_k_2164_);
return v_k_2164_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg___boxed(lean_object* v_k_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_IO_TaskState_ctorElim___redArg(v_k_2165_);
lean_dec(v_k_2165_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim(lean_object* v_motive_2167_, lean_object* v_ctorIdx_2168_, uint8_t v_t_2169_, lean_object* v_h_2170_, lean_object* v_k_2171_){
_start:
{
lean_inc(v_k_2171_);
return v_k_2171_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___boxed(lean_object* v_motive_2172_, lean_object* v_ctorIdx_2173_, lean_object* v_t_2174_, lean_object* v_h_2175_, lean_object* v_k_2176_){
_start:
{
uint8_t v_t_boxed_2177_; lean_object* v_res_2178_; 
v_t_boxed_2177_ = lean_unbox(v_t_2174_);
v_res_2178_ = l_IO_TaskState_ctorElim(v_motive_2172_, v_ctorIdx_2173_, v_t_boxed_2177_, v_h_2175_, v_k_2176_);
lean_dec(v_k_2176_);
lean_dec(v_ctorIdx_2173_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg(lean_object* v_waiting_2179_){
_start:
{
lean_inc(v_waiting_2179_);
return v_waiting_2179_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg___boxed(lean_object* v_waiting_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_IO_TaskState_waiting_elim___redArg(v_waiting_2180_);
lean_dec(v_waiting_2180_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim(lean_object* v_motive_2182_, uint8_t v_t_2183_, lean_object* v_h_2184_, lean_object* v_waiting_2185_){
_start:
{
lean_inc(v_waiting_2185_);
return v_waiting_2185_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___boxed(lean_object* v_motive_2186_, lean_object* v_t_2187_, lean_object* v_h_2188_, lean_object* v_waiting_2189_){
_start:
{
uint8_t v_t_boxed_2190_; lean_object* v_res_2191_; 
v_t_boxed_2190_ = lean_unbox(v_t_2187_);
v_res_2191_ = l_IO_TaskState_waiting_elim(v_motive_2186_, v_t_boxed_2190_, v_h_2188_, v_waiting_2189_);
lean_dec(v_waiting_2189_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg(lean_object* v_running_2192_){
_start:
{
lean_inc(v_running_2192_);
return v_running_2192_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg___boxed(lean_object* v_running_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_IO_TaskState_running_elim___redArg(v_running_2193_);
lean_dec(v_running_2193_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim(lean_object* v_motive_2195_, uint8_t v_t_2196_, lean_object* v_h_2197_, lean_object* v_running_2198_){
_start:
{
lean_inc(v_running_2198_);
return v_running_2198_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___boxed(lean_object* v_motive_2199_, lean_object* v_t_2200_, lean_object* v_h_2201_, lean_object* v_running_2202_){
_start:
{
uint8_t v_t_boxed_2203_; lean_object* v_res_2204_; 
v_t_boxed_2203_ = lean_unbox(v_t_2200_);
v_res_2204_ = l_IO_TaskState_running_elim(v_motive_2199_, v_t_boxed_2203_, v_h_2201_, v_running_2202_);
lean_dec(v_running_2202_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg(lean_object* v_finished_2205_){
_start:
{
lean_inc(v_finished_2205_);
return v_finished_2205_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg___boxed(lean_object* v_finished_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_IO_TaskState_finished_elim___redArg(v_finished_2206_);
lean_dec(v_finished_2206_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim(lean_object* v_motive_2208_, uint8_t v_t_2209_, lean_object* v_h_2210_, lean_object* v_finished_2211_){
_start:
{
lean_inc(v_finished_2211_);
return v_finished_2211_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___boxed(lean_object* v_motive_2212_, lean_object* v_t_2213_, lean_object* v_h_2214_, lean_object* v_finished_2215_){
_start:
{
uint8_t v_t_boxed_2216_; lean_object* v_res_2217_; 
v_t_boxed_2216_ = lean_unbox(v_t_2213_);
v_res_2217_ = l_IO_TaskState_finished_elim(v_motive_2212_, v_t_boxed_2216_, v_h_2214_, v_finished_2215_);
lean_dec(v_finished_2215_);
return v_res_2217_;
}
}
static uint8_t _init_l_IO_instInhabitedTaskState_default(void){
_start:
{
uint8_t v___x_2218_; 
v___x_2218_ = 0;
return v___x_2218_;
}
}
static uint8_t _init_l_IO_instInhabitedTaskState(void){
_start:
{
uint8_t v___x_2219_; 
v___x_2219_ = 0;
return v___x_2219_;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__6(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_unsigned_to_nat(2u);
v___x_2230_ = lean_nat_to_int(v___x_2229_);
return v___x_2230_;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__7(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = lean_unsigned_to_nat(1u);
v___x_2232_ = lean_nat_to_int(v___x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr(uint8_t v_x_2233_, lean_object* v_prec_2234_){
_start:
{
lean_object* v___y_2236_; lean_object* v___y_2243_; lean_object* v___y_2250_; 
switch(v_x_2233_)
{
case 0:
{
lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2256_ = lean_unsigned_to_nat(1024u);
v___x_2257_ = lean_nat_dec_le(v___x_2256_, v_prec_2234_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2236_ = v___x_2258_;
goto v___jp_2235_;
}
else
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2236_ = v___x_2259_;
goto v___jp_2235_;
}
}
case 1:
{
lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2260_ = lean_unsigned_to_nat(1024u);
v___x_2261_ = lean_nat_dec_le(v___x_2260_, v_prec_2234_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; 
v___x_2262_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2243_ = v___x_2262_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2263_; 
v___x_2263_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2243_ = v___x_2263_;
goto v___jp_2242_;
}
}
default: 
{
lean_object* v___x_2264_; uint8_t v___x_2265_; 
v___x_2264_ = lean_unsigned_to_nat(1024u);
v___x_2265_ = lean_nat_dec_le(v___x_2264_, v_prec_2234_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2250_ = v___x_2266_;
goto v___jp_2249_;
}
else
{
lean_object* v___x_2267_; 
v___x_2267_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2250_ = v___x_2267_;
goto v___jp_2249_;
}
}
}
v___jp_2235_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2237_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__1));
lean_inc(v___y_2236_);
v___x_2238_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___y_2236_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = 0;
v___x_2240_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*1, v___x_2239_);
v___x_2241_ = l_Repr_addAppParen(v___x_2240_, v_prec_2234_);
return v___x_2241_;
}
v___jp_2242_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2244_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__3));
lean_inc(v___y_2243_);
v___x_2245_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___y_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = 0;
v___x_2247_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2247_, 0, v___x_2245_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*1, v___x_2246_);
v___x_2248_ = l_Repr_addAppParen(v___x_2247_, v_prec_2234_);
return v___x_2248_;
}
v___jp_2249_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; uint8_t v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2251_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__5));
lean_inc(v___y_2250_);
v___x_2252_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___y_2250_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = 0;
v___x_2254_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set_uint8(v___x_2254_, sizeof(void*)*1, v___x_2253_);
v___x_2255_ = l_Repr_addAppParen(v___x_2254_, v_prec_2234_);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr___boxed(lean_object* v_x_2268_, lean_object* v_prec_2269_){
_start:
{
uint8_t v_x_177__boxed_2270_; lean_object* v_res_2271_; 
v_x_177__boxed_2270_ = lean_unbox(v_x_2268_);
v_res_2271_ = l_IO_instReprTaskState_repr(v_x_177__boxed_2270_, v_prec_2269_);
lean_dec(v_prec_2269_);
return v_res_2271_;
}
}
LEAN_EXPORT uint8_t l_IO_TaskState_ofNat(lean_object* v_n_2274_){
_start:
{
lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = lean_unsigned_to_nat(0u);
v___x_2276_ = lean_nat_dec_le(v_n_2274_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2277_ = lean_unsigned_to_nat(1u);
v___x_2278_ = lean_nat_dec_le(v_n_2274_, v___x_2277_);
if (v___x_2278_ == 0)
{
uint8_t v___x_2279_; 
v___x_2279_ = 2;
return v___x_2279_;
}
else
{
uint8_t v___x_2280_; 
v___x_2280_ = 1;
return v___x_2280_;
}
}
else
{
uint8_t v___x_2281_; 
v___x_2281_ = 0;
return v___x_2281_;
}
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ofNat___boxed(lean_object* v_n_2282_){
_start:
{
uint8_t v_res_2283_; lean_object* v_r_2284_; 
v_res_2283_ = l_IO_TaskState_ofNat(v_n_2282_);
lean_dec(v_n_2282_);
v_r_2284_ = lean_box(v_res_2283_);
return v_r_2284_;
}
}
LEAN_EXPORT uint8_t l_IO_instDecidableEqTaskState(uint8_t v_x_2285_, uint8_t v_y_2286_){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2287_ = l_IO_TaskState_ctorIdx(v_x_2285_);
v___x_2288_ = l_IO_TaskState_ctorIdx(v_y_2286_);
v___x_2289_ = lean_nat_dec_eq(v___x_2287_, v___x_2288_);
lean_dec(v___x_2288_);
lean_dec(v___x_2287_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_IO_instDecidableEqTaskState___boxed(lean_object* v_x_2290_, lean_object* v_y_2291_){
_start:
{
uint8_t v_x_13__boxed_2292_; uint8_t v_y_14__boxed_2293_; uint8_t v_res_2294_; lean_object* v_r_2295_; 
v_x_13__boxed_2292_ = lean_unbox(v_x_2290_);
v_y_14__boxed_2293_ = lean_unbox(v_y_2291_);
v_res_2294_ = l_IO_instDecidableEqTaskState(v_x_13__boxed_2292_, v_y_14__boxed_2293_);
v_r_2295_ = lean_box(v_res_2294_);
return v_r_2295_;
}
}
LEAN_EXPORT uint8_t l_IO_instOrdTaskState_ord(uint8_t v_x_2296_, uint8_t v_y_2297_){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2298_ = l_IO_TaskState_ctorIdx(v_x_2296_);
v___x_2299_ = l_IO_TaskState_ctorIdx(v_y_2297_);
v___x_2300_ = lean_nat_dec_lt(v___x_2298_, v___x_2299_);
if (v___x_2300_ == 0)
{
uint8_t v___x_2301_; 
v___x_2301_ = lean_nat_dec_eq(v___x_2298_, v___x_2299_);
lean_dec(v___x_2299_);
lean_dec(v___x_2298_);
if (v___x_2301_ == 0)
{
uint8_t v___x_2302_; 
v___x_2302_ = 2;
return v___x_2302_;
}
else
{
uint8_t v___x_2303_; 
v___x_2303_ = 1;
return v___x_2303_;
}
}
else
{
uint8_t v___x_2304_; 
lean_dec(v___x_2299_);
lean_dec(v___x_2298_);
v___x_2304_ = 0;
return v___x_2304_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instOrdTaskState_ord___boxed(lean_object* v_x_2305_, lean_object* v_y_2306_){
_start:
{
uint8_t v_x_30__boxed_2307_; uint8_t v_y_31__boxed_2308_; uint8_t v_res_2309_; lean_object* v_r_2310_; 
v_x_30__boxed_2307_ = lean_unbox(v_x_2305_);
v_y_31__boxed_2308_ = lean_unbox(v_y_2306_);
v_res_2309_ = l_IO_instOrdTaskState_ord(v_x_30__boxed_2307_, v_y_31__boxed_2308_);
v_r_2310_ = lean_box(v_res_2309_);
return v_r_2310_;
}
}
static lean_object* _init_l_IO_instLTTaskState(void){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_box(0);
return v___x_2313_;
}
}
static lean_object* _init_l_IO_instLETaskState(void){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_box(0);
return v___x_2314_;
}
}
LEAN_EXPORT uint8_t l_IO_instMinTaskState___lam__0(uint8_t v_x_2315_, uint8_t v_y_2316_){
_start:
{
uint8_t v___x_2317_; 
v___x_2317_ = l_IO_instOrdTaskState_ord(v_x_2315_, v_y_2316_);
if (v___x_2317_ == 2)
{
return v_y_2316_;
}
else
{
return v_x_2315_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instMinTaskState___lam__0___boxed(lean_object* v_x_2318_, lean_object* v_y_2319_){
_start:
{
uint8_t v_x_boxed_2320_; uint8_t v_y_boxed_2321_; uint8_t v_res_2322_; lean_object* v_r_2323_; 
v_x_boxed_2320_ = lean_unbox(v_x_2318_);
v_y_boxed_2321_ = lean_unbox(v_y_2319_);
v_res_2322_ = l_IO_instMinTaskState___lam__0(v_x_boxed_2320_, v_y_boxed_2321_);
v_r_2323_ = lean_box(v_res_2322_);
return v_r_2323_;
}
}
LEAN_EXPORT uint8_t l_IO_instMaxTaskState___lam__0(uint8_t v_x_2326_, uint8_t v_y_2327_){
_start:
{
uint8_t v___x_2328_; 
v___x_2328_ = l_IO_instOrdTaskState_ord(v_x_2326_, v_y_2327_);
if (v___x_2328_ == 2)
{
return v_x_2326_;
}
else
{
return v_y_2327_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instMaxTaskState___lam__0___boxed(lean_object* v_x_2329_, lean_object* v_y_2330_){
_start:
{
uint8_t v_x_boxed_2331_; uint8_t v_y_boxed_2332_; uint8_t v_res_2333_; lean_object* v_r_2334_; 
v_x_boxed_2331_ = lean_unbox(v_x_2329_);
v_y_boxed_2332_ = lean_unbox(v_y_2330_);
v_res_2333_ = l_IO_instMaxTaskState___lam__0(v_x_boxed_2331_, v_y_boxed_2332_);
v_r_2334_ = lean_box(v_res_2333_);
return v_r_2334_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toString(uint8_t v_x_2340_){
_start:
{
switch(v_x_2340_)
{
case 0:
{
lean_object* v___x_2341_; 
v___x_2341_ = ((lean_object*)(l_IO_TaskState_toString___closed__0));
return v___x_2341_;
}
case 1:
{
lean_object* v___x_2342_; 
v___x_2342_ = ((lean_object*)(l_IO_TaskState_toString___closed__1));
return v___x_2342_;
}
default: 
{
lean_object* v___x_2343_; 
v___x_2343_ = ((lean_object*)(l_IO_TaskState_toString___closed__2));
return v___x_2343_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toString___boxed(lean_object* v_x_2344_){
_start:
{
uint8_t v_x_31__boxed_2345_; lean_object* v_res_2346_; 
v_x_31__boxed_2345_ = lean_unbox(v_x_2344_);
v_res_2346_ = l_IO_TaskState_toString(v_x_31__boxed_2345_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_IO_getTaskState___boxed(lean_object* v_00_u03b1_2352_, lean_object* v_a_00___x40___internal___hyg_2353_, lean_object* v_a_00___x40___internal___hyg_2354_){
_start:
{
uint8_t v_res_2355_; lean_object* v_r_2356_; 
v_res_2355_ = lean_io_get_task_state(v_a_00___x40___internal___hyg_2353_);
lean_dec_ref(v_a_00___x40___internal___hyg_2353_);
v_r_2356_ = lean_box(v_res_2355_);
return v_r_2356_;
}
}
LEAN_EXPORT uint8_t l_IO_hasFinished___redArg(lean_object* v_task_2357_){
_start:
{
uint8_t v___x_2359_; 
v___x_2359_ = lean_io_get_task_state(v_task_2357_);
if (v___x_2359_ == 2)
{
uint8_t v___x_2360_; 
v___x_2360_ = 1;
return v___x_2360_;
}
else
{
uint8_t v___x_2361_; 
v___x_2361_ = 0;
return v___x_2361_;
}
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___redArg___boxed(lean_object* v_task_2362_, lean_object* v_a_2363_){
_start:
{
uint8_t v_res_2364_; lean_object* v_r_2365_; 
v_res_2364_ = l_IO_hasFinished___redArg(v_task_2362_);
lean_dec_ref(v_task_2362_);
v_r_2365_ = lean_box(v_res_2364_);
return v_r_2365_;
}
}
LEAN_EXPORT uint8_t l_IO_hasFinished(lean_object* v_00_u03b1_2366_, lean_object* v_task_2367_){
_start:
{
uint8_t v___x_2369_; 
v___x_2369_ = lean_io_get_task_state(v_task_2367_);
if (v___x_2369_ == 2)
{
uint8_t v___x_2370_; 
v___x_2370_ = 1;
return v___x_2370_;
}
else
{
uint8_t v___x_2371_; 
v___x_2371_ = 0;
return v___x_2371_;
}
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object* v_00_u03b1_2372_, lean_object* v_task_2373_, lean_object* v_a_2374_){
_start:
{
uint8_t v_res_2375_; lean_object* v_r_2376_; 
v_res_2375_ = l_IO_hasFinished(v_00_u03b1_2372_, v_task_2373_);
lean_dec_ref(v_task_2373_);
v_r_2376_ = lean_box(v_res_2375_);
return v_r_2376_;
}
}
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object* v_00_u03b1_2380_, lean_object* v_t_2381_, lean_object* v_a_00___x40___internal___hyg_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = lean_io_wait(v_t_2381_);
return v_res_2383_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__10));
v___x_2411_ = l_Lean_mkAtom(v___x_2410_);
return v___x_2411_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__12, &l_IO_waitAny___auto__1___closed__12_once, _init_l_IO_waitAny___auto__1___closed__12);
v___x_2413_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2414_ = lean_array_push(v___x_2413_, v___x_2412_);
return v___x_2414_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__17));
v___x_2424_ = lean_string_utf8_byte_size(v___x_2423_);
return v___x_2424_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2425_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__18, &l_IO_waitAny___auto__1___closed__18_once, _init_l_IO_waitAny___auto__1___closed__18);
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__17));
v___x_2428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v___x_2426_);
lean_ctor_set(v___x_2428_, 2, v___x_2425_);
return v___x_2428_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2434_ = lean_box(0);
v___x_2435_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__22));
v___x_2436_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__19, &l_IO_waitAny___auto__1___closed__19_once, _init_l_IO_waitAny___auto__1___closed__19);
v___x_2437_ = lean_box(2);
v___x_2438_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set(v___x_2438_, 1, v___x_2436_);
lean_ctor_set(v___x_2438_, 2, v___x_2435_);
lean_ctor_set(v___x_2438_, 3, v___x_2434_);
return v___x_2438_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__23, &l_IO_waitAny___auto__1___closed__23_once, _init_l_IO_waitAny___auto__1___closed__23);
v___x_2440_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2441_ = lean_array_push(v___x_2440_, v___x_2439_);
return v___x_2441_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__28(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__27));
v___x_2450_ = l_Lean_mkAtom(v___x_2449_);
return v___x_2450_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__29(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__28, &l_IO_waitAny___auto__1___closed__28_once, _init_l_IO_waitAny___auto__1___closed__28);
v___x_2452_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2453_ = lean_array_push(v___x_2452_, v___x_2451_);
return v___x_2453_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__30(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2454_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__29, &l_IO_waitAny___auto__1___closed__29_once, _init_l_IO_waitAny___auto__1___closed__29);
v___x_2455_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__26));
v___x_2456_ = lean_box(2);
v___x_2457_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
lean_ctor_set(v___x_2457_, 1, v___x_2455_);
lean_ctor_set(v___x_2457_, 2, v___x_2454_);
return v___x_2457_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__31(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__30, &l_IO_waitAny___auto__1___closed__30_once, _init_l_IO_waitAny___auto__1___closed__30);
v___x_2459_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2460_ = lean_array_push(v___x_2459_, v___x_2458_);
return v___x_2460_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__32(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2461_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__31, &l_IO_waitAny___auto__1___closed__31_once, _init_l_IO_waitAny___auto__1___closed__31);
v___x_2462_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_2463_ = lean_box(2);
v___x_2464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___x_2462_);
lean_ctor_set(v___x_2464_, 2, v___x_2461_);
return v___x_2464_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__33(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__32, &l_IO_waitAny___auto__1___closed__32_once, _init_l_IO_waitAny___auto__1___closed__32);
v___x_2466_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__24, &l_IO_waitAny___auto__1___closed__24_once, _init_l_IO_waitAny___auto__1___closed__24);
v___x_2467_ = lean_array_push(v___x_2466_, v___x_2465_);
return v___x_2467_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__34(void){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2468_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__33, &l_IO_waitAny___auto__1___closed__33_once, _init_l_IO_waitAny___auto__1___closed__33);
v___x_2469_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_2470_ = lean_box(2);
v___x_2471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
lean_ctor_set(v___x_2471_, 1, v___x_2469_);
lean_ctor_set(v___x_2471_, 2, v___x_2468_);
return v___x_2471_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__35(void){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2472_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__34, &l_IO_waitAny___auto__1___closed__34_once, _init_l_IO_waitAny___auto__1___closed__34);
v___x_2473_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__13, &l_IO_waitAny___auto__1___closed__13_once, _init_l_IO_waitAny___auto__1___closed__13);
v___x_2474_ = lean_array_push(v___x_2473_, v___x_2472_);
return v___x_2474_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__36(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2475_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__35, &l_IO_waitAny___auto__1___closed__35_once, _init_l_IO_waitAny___auto__1___closed__35);
v___x_2476_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__11));
v___x_2477_ = lean_box(2);
v___x_2478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
lean_ctor_set(v___x_2478_, 1, v___x_2476_);
lean_ctor_set(v___x_2478_, 2, v___x_2475_);
return v___x_2478_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__37(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__36, &l_IO_waitAny___auto__1___closed__36_once, _init_l_IO_waitAny___auto__1___closed__36);
v___x_2480_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2481_ = lean_array_push(v___x_2480_, v___x_2479_);
return v___x_2481_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__38(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2482_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__37, &l_IO_waitAny___auto__1___closed__37_once, _init_l_IO_waitAny___auto__1___closed__37);
v___x_2483_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_2484_ = lean_box(2);
v___x_2485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
lean_ctor_set(v___x_2485_, 1, v___x_2483_);
lean_ctor_set(v___x_2485_, 2, v___x_2482_);
return v___x_2485_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__39(void){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2486_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__38, &l_IO_waitAny___auto__1___closed__38_once, _init_l_IO_waitAny___auto__1___closed__38);
v___x_2487_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2488_ = lean_array_push(v___x_2487_, v___x_2486_);
return v___x_2488_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__40(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2489_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__39, &l_IO_waitAny___auto__1___closed__39_once, _init_l_IO_waitAny___auto__1___closed__39);
v___x_2490_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__7));
v___x_2491_ = lean_box(2);
v___x_2492_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
lean_ctor_set(v___x_2492_, 1, v___x_2490_);
lean_ctor_set(v___x_2492_, 2, v___x_2489_);
return v___x_2492_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__41(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__40, &l_IO_waitAny___auto__1___closed__40_once, _init_l_IO_waitAny___auto__1___closed__40);
v___x_2494_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2495_ = lean_array_push(v___x_2494_, v___x_2493_);
return v___x_2495_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__42(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2496_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__41, &l_IO_waitAny___auto__1___closed__41_once, _init_l_IO_waitAny___auto__1___closed__41);
v___x_2497_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__4));
v___x_2498_ = lean_box(2);
v___x_2499_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v___x_2497_);
lean_ctor_set(v___x_2499_, 2, v___x_2496_);
return v___x_2499_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1(void){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__42, &l_IO_waitAny___auto__1___closed__42_once, _init_l_IO_waitAny___auto__1___closed__42);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object* v_00_u03b1_2505_, lean_object* v_tasks_2506_, lean_object* v_h_2507_, lean_object* v_a_00___x40___internal___hyg_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = lean_io_wait_any(v_tasks_2506_);
lean_dec(v_tasks_2506_);
return v_res_2509_;
}
}
static lean_object* _init_l_IO_waitAny_x27___auto__1(void){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__42, &l_IO_waitAny___auto__1___closed__42_once, _init_l_IO_waitAny___auto__1___closed__42);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0(lean_object* v___x_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v_a_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
if (lean_obj_tag(v_a_2514_) == 0)
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_array_to_list(v_a_2515_);
return v___x_2516_;
}
else
{
lean_object* v_head_2517_; lean_object* v_tail_2518_; lean_object* v___x_2519_; lean_object* v___f_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_head_2517_ = lean_ctor_get(v_a_2514_, 0);
lean_inc(v_head_2517_);
v_tail_2518_ = lean_ctor_get(v_a_2514_, 1);
lean_inc(v_tail_2518_);
lean_dec_ref(v_a_2514_);
v___x_2519_ = lean_array_get_size(v_a_2515_);
v___f_2520_ = lean_alloc_closure((void*)(l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2520_, 0, v___x_2519_);
v___x_2521_ = lean_unsigned_to_nat(0u);
v___x_2522_ = 1;
v___x_2523_ = lean_task_map(v___f_2520_, v_head_2517_, v___x_2521_, v___x_2522_);
v___x_2524_ = lean_array_push(v_a_2515_, v___x_2523_);
v_a_2514_ = v_tail_2518_;
v_a_2515_ = v___x_2524_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg(lean_object* v_tasks_2528_){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v_fst_2533_; lean_object* v_snd_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2542_; 
v___x_2530_ = ((lean_object*)(l_IO_waitAny_x27___redArg___closed__0));
lean_inc(v_tasks_2528_);
v___x_2531_ = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(v_tasks_2528_, v___x_2530_);
v___x_2532_ = lean_io_wait_any(v___x_2531_);
lean_dec(v___x_2531_);
v_fst_2533_ = lean_ctor_get(v___x_2532_, 0);
v_snd_2534_ = lean_ctor_get(v___x_2532_, 1);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2536_ = v___x_2532_;
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_snd_2534_);
lean_inc(v_fst_2533_);
lean_dec(v___x_2532_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
lean_inc(v_tasks_2528_);
v___x_2538_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_box(0), v_tasks_2528_, v_tasks_2528_, v_fst_2533_, v___x_2530_);
lean_dec(v_tasks_2528_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 1, v___x_2538_);
lean_ctor_set(v___x_2536_, 0, v_snd_2534_);
v___x_2540_ = v___x_2536_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_snd_2534_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg___boxed(lean_object* v_tasks_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_IO_waitAny_x27___redArg(v_tasks_2543_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27(lean_object* v_00_u03b1_2546_, lean_object* v_tasks_2547_, lean_object* v_h_2548_){
_start:
{
lean_object* v___x_2550_; 
v___x_2550_ = l_IO_waitAny_x27___redArg(v_tasks_2547_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___boxed(lean_object* v_00_u03b1_2551_, lean_object* v_tasks_2552_, lean_object* v_h_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_IO_waitAny_x27(v_00_u03b1_2551_, v_tasks_2552_, v_h_2553_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0(lean_object* v_00_u03b1_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(v_a_2557_, v_a_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object* v_a_00___x40___internal___hyg_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = lean_io_get_num_heartbeats();
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_IO_setNumHeartbeats___boxed(lean_object* v_count_2565_, lean_object* v_a_00___x40___internal___hyg_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = lean_io_set_heartbeats(v_count_2565_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_IO_addHeartbeats(lean_object* v_count_2568_){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = lean_io_get_num_heartbeats();
v___x_2571_ = lean_nat_add(v___x_2570_, v_count_2568_);
lean_dec(v___x_2570_);
v___x_2572_ = lean_io_set_heartbeats(v___x_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_IO_addHeartbeats___boxed(lean_object* v_count_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_IO_addHeartbeats(v_count_2573_);
lean_dec(v_count_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx(uint8_t v_x_2576_){
_start:
{
switch(v_x_2576_)
{
case 0:
{
lean_object* v___x_2577_; 
v___x_2577_ = lean_unsigned_to_nat(0u);
return v___x_2577_;
}
case 1:
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_unsigned_to_nat(1u);
return v___x_2578_;
}
case 2:
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_unsigned_to_nat(2u);
return v___x_2579_;
}
case 3:
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_unsigned_to_nat(3u);
return v___x_2580_;
}
default: 
{
lean_object* v___x_2581_; 
v___x_2581_ = lean_unsigned_to_nat(4u);
return v___x_2581_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx___boxed(lean_object* v_x_2582_){
_start:
{
uint8_t v_x_boxed_2583_; lean_object* v_res_2584_; 
v_x_boxed_2583_ = lean_unbox(v_x_2582_);
v_res_2584_ = l_IO_FS_Mode_ctorIdx(v_x_boxed_2583_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx(uint8_t v_x_2585_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_IO_FS_Mode_ctorIdx(v_x_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_toCtorIdx___boxed(lean_object* v_x_2587_){
_start:
{
uint8_t v_x_4__boxed_2588_; lean_object* v_res_2589_; 
v_x_4__boxed_2588_ = lean_unbox(v_x_2587_);
v_res_2589_ = l_IO_FS_Mode_toCtorIdx(v_x_4__boxed_2588_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg(lean_object* v_k_2590_){
_start:
{
lean_inc(v_k_2590_);
return v_k_2590_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg___boxed(lean_object* v_k_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_IO_FS_Mode_ctorElim___redArg(v_k_2591_);
lean_dec(v_k_2591_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim(lean_object* v_motive_2593_, lean_object* v_ctorIdx_2594_, uint8_t v_t_2595_, lean_object* v_h_2596_, lean_object* v_k_2597_){
_start:
{
lean_inc(v_k_2597_);
return v_k_2597_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___boxed(lean_object* v_motive_2598_, lean_object* v_ctorIdx_2599_, lean_object* v_t_2600_, lean_object* v_h_2601_, lean_object* v_k_2602_){
_start:
{
uint8_t v_t_boxed_2603_; lean_object* v_res_2604_; 
v_t_boxed_2603_ = lean_unbox(v_t_2600_);
v_res_2604_ = l_IO_FS_Mode_ctorElim(v_motive_2598_, v_ctorIdx_2599_, v_t_boxed_2603_, v_h_2601_, v_k_2602_);
lean_dec(v_k_2602_);
lean_dec(v_ctorIdx_2599_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg(lean_object* v_read_2605_){
_start:
{
lean_inc(v_read_2605_);
return v_read_2605_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg___boxed(lean_object* v_read_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_IO_FS_Mode_read_elim___redArg(v_read_2606_);
lean_dec(v_read_2606_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim(lean_object* v_motive_2608_, uint8_t v_t_2609_, lean_object* v_h_2610_, lean_object* v_read_2611_){
_start:
{
lean_inc(v_read_2611_);
return v_read_2611_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___boxed(lean_object* v_motive_2612_, lean_object* v_t_2613_, lean_object* v_h_2614_, lean_object* v_read_2615_){
_start:
{
uint8_t v_t_boxed_2616_; lean_object* v_res_2617_; 
v_t_boxed_2616_ = lean_unbox(v_t_2613_);
v_res_2617_ = l_IO_FS_Mode_read_elim(v_motive_2612_, v_t_boxed_2616_, v_h_2614_, v_read_2615_);
lean_dec(v_read_2615_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg(lean_object* v_write_2618_){
_start:
{
lean_inc(v_write_2618_);
return v_write_2618_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg___boxed(lean_object* v_write_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_IO_FS_Mode_write_elim___redArg(v_write_2619_);
lean_dec(v_write_2619_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim(lean_object* v_motive_2621_, uint8_t v_t_2622_, lean_object* v_h_2623_, lean_object* v_write_2624_){
_start:
{
lean_inc(v_write_2624_);
return v_write_2624_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___boxed(lean_object* v_motive_2625_, lean_object* v_t_2626_, lean_object* v_h_2627_, lean_object* v_write_2628_){
_start:
{
uint8_t v_t_boxed_2629_; lean_object* v_res_2630_; 
v_t_boxed_2629_ = lean_unbox(v_t_2626_);
v_res_2630_ = l_IO_FS_Mode_write_elim(v_motive_2625_, v_t_boxed_2629_, v_h_2627_, v_write_2628_);
lean_dec(v_write_2628_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg(lean_object* v_writeNew_2631_){
_start:
{
lean_inc(v_writeNew_2631_);
return v_writeNew_2631_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg___boxed(lean_object* v_writeNew_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_IO_FS_Mode_writeNew_elim___redArg(v_writeNew_2632_);
lean_dec(v_writeNew_2632_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim(lean_object* v_motive_2634_, uint8_t v_t_2635_, lean_object* v_h_2636_, lean_object* v_writeNew_2637_){
_start:
{
lean_inc(v_writeNew_2637_);
return v_writeNew_2637_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___boxed(lean_object* v_motive_2638_, lean_object* v_t_2639_, lean_object* v_h_2640_, lean_object* v_writeNew_2641_){
_start:
{
uint8_t v_t_boxed_2642_; lean_object* v_res_2643_; 
v_t_boxed_2642_ = lean_unbox(v_t_2639_);
v_res_2643_ = l_IO_FS_Mode_writeNew_elim(v_motive_2638_, v_t_boxed_2642_, v_h_2640_, v_writeNew_2641_);
lean_dec(v_writeNew_2641_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg(lean_object* v_readWrite_2644_){
_start:
{
lean_inc(v_readWrite_2644_);
return v_readWrite_2644_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg___boxed(lean_object* v_readWrite_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_IO_FS_Mode_readWrite_elim___redArg(v_readWrite_2645_);
lean_dec(v_readWrite_2645_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim(lean_object* v_motive_2647_, uint8_t v_t_2648_, lean_object* v_h_2649_, lean_object* v_readWrite_2650_){
_start:
{
lean_inc(v_readWrite_2650_);
return v_readWrite_2650_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___boxed(lean_object* v_motive_2651_, lean_object* v_t_2652_, lean_object* v_h_2653_, lean_object* v_readWrite_2654_){
_start:
{
uint8_t v_t_boxed_2655_; lean_object* v_res_2656_; 
v_t_boxed_2655_ = lean_unbox(v_t_2652_);
v_res_2656_ = l_IO_FS_Mode_readWrite_elim(v_motive_2651_, v_t_boxed_2655_, v_h_2653_, v_readWrite_2654_);
lean_dec(v_readWrite_2654_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg(lean_object* v_append_2657_){
_start:
{
lean_inc(v_append_2657_);
return v_append_2657_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg___boxed(lean_object* v_append_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_IO_FS_Mode_append_elim___redArg(v_append_2658_);
lean_dec(v_append_2658_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim(lean_object* v_motive_2660_, uint8_t v_t_2661_, lean_object* v_h_2662_, lean_object* v_append_2663_){
_start:
{
lean_inc(v_append_2663_);
return v_append_2663_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___boxed(lean_object* v_motive_2664_, lean_object* v_t_2665_, lean_object* v_h_2666_, lean_object* v_append_2667_){
_start:
{
uint8_t v_t_boxed_2668_; lean_object* v_res_2669_; 
v_t_boxed_2668_ = lean_unbox(v_t_2665_);
v_res_2669_ = l_IO_FS_Mode_append_elim(v_motive_2664_, v_t_boxed_2668_, v_h_2666_, v_append_2667_);
lean_dec(v_append_2667_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0(){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0___boxed(lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_IO_FS_instInhabitedStream_default___lam__0();
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1(){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1___boxed(lean_object* v___y_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_IO_FS_instInhabitedStream_default___lam__1();
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2(lean_object* v_x_2683_){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2___boxed(lean_object* v_x_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_IO_FS_instInhabitedStream_default___lam__2(v_x_2687_);
lean_dec_ref(v_x_2687_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3(lean_object* v_x_2690_){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3___boxed(lean_object* v_x_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_IO_FS_instInhabitedStream_default___lam__3(v_x_2694_);
lean_dec_ref(v_x_2694_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4(size_t v_x_2697_){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4___boxed(lean_object* v_x_2701_, lean_object* v___y_2702_){
_start:
{
size_t v_x_193__boxed_2703_; lean_object* v_res_2704_; 
v_x_193__boxed_2703_ = lean_unbox_usize(v_x_2701_);
lean_dec(v_x_2701_);
v_res_2704_ = l_IO_FS_instInhabitedStream_default___lam__4(v_x_193__boxed_2703_);
return v_res_2704_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instInhabitedStream_default___lam__5(uint8_t v___x_2705_){
_start:
{
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__5___boxed(lean_object* v___x_2707_, lean_object* v___y_2708_){
_start:
{
uint8_t v___x_204__boxed_2709_; uint8_t v_res_2710_; lean_object* v_r_2711_; 
v___x_204__boxed_2709_ = lean_unbox(v___x_2707_);
v_res_2710_ = l_IO_FS_instInhabitedStream_default___lam__5(v___x_204__boxed_2709_);
v_r_2711_ = lean_box(v_res_2710_);
return v_r_2711_;
}
}
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object* v_a_00___x40___internal___hyg_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = lean_get_stdin();
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object* v_a_00___x40___internal___hyg_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = lean_get_stdout();
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object* v_a_00___x40___internal___hyg_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = lean_get_stderr();
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object* v_a_00___x40___internal___hyg_2740_, lean_object* v_a_00___x40___internal___hyg_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = lean_get_set_stdin(v_a_00___x40___internal___hyg_2740_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object* v_a_00___x40___internal___hyg_2745_, lean_object* v_a_00___x40___internal___hyg_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = lean_get_set_stdout(v_a_00___x40___internal___hyg_2745_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object* v_a_00___x40___internal___hyg_2750_, lean_object* v_a_00___x40___internal___hyg_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = lean_get_set_stderr(v_a_00___x40___internal___hyg_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_IO_iterate___redArg(lean_object* v_a_2753_, lean_object* v_f_2754_){
_start:
{
lean_object* v___x_2756_; 
lean_inc_ref(v_f_2754_);
v___x_2756_ = lean_apply_2(v_f_2754_, v_a_2753_, lean_box(0));
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2767_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2767_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2767_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
if (lean_obj_tag(v_a_2757_) == 0)
{
lean_object* v_val_2761_; 
lean_del_object(v___x_2759_);
v_val_2761_ = lean_ctor_get(v_a_2757_, 0);
lean_inc(v_val_2761_);
lean_dec_ref(v_a_2757_);
v_a_2753_ = v_val_2761_;
goto _start;
}
else
{
lean_object* v_val_2763_; lean_object* v___x_2765_; 
lean_dec_ref(v_f_2754_);
v_val_2763_ = lean_ctor_get(v_a_2757_, 0);
lean_inc(v_val_2763_);
lean_dec_ref(v_a_2757_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v_val_2763_);
v___x_2765_ = v___x_2759_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_val_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec_ref(v_f_2754_);
v_a_2768_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2756_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2756_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_iterate___redArg___boxed(lean_object* v_a_2776_, lean_object* v_f_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_IO_iterate___redArg(v_a_2776_, v_f_2777_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_IO_iterate(lean_object* v_00_u03b1_2780_, lean_object* v_00_u03b2_2781_, lean_object* v_a_2782_, lean_object* v_f_2783_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_IO_iterate___redArg(v_a_2782_, v_f_2783_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_IO_iterate___boxed(lean_object* v_00_u03b1_2786_, lean_object* v_00_u03b2_2787_, lean_object* v_a_2788_, lean_object* v_f_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_IO_iterate(v_00_u03b1_2786_, v_00_u03b2_2787_, v_a_2788_, v_f_2789_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object* v_fn_2795_, lean_object* v_mode_2796_, lean_object* v_a_00___x40___internal___hyg_2797_){
_start:
{
uint8_t v_mode_boxed_2798_; lean_object* v_res_2799_; 
v_mode_boxed_2798_ = lean_unbox(v_mode_2796_);
v_res_2799_ = lean_io_prim_handle_mk(v_fn_2795_, v_mode_boxed_2798_);
lean_dec_ref(v_fn_2795_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lock___boxed(lean_object* v_h_2803_, lean_object* v_exclusive_2804_, lean_object* v_a_00___x40___internal___hyg_2805_){
_start:
{
uint8_t v_exclusive_boxed_2806_; lean_object* v_res_2807_; 
v_exclusive_boxed_2806_ = lean_unbox(v_exclusive_2804_);
v_res_2807_ = lean_io_prim_handle_lock(v_h_2803_, v_exclusive_boxed_2806_);
lean_dec(v_h_2803_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_tryLock___boxed(lean_object* v_h_2811_, lean_object* v_exclusive_2812_, lean_object* v_a_00___x40___internal___hyg_2813_){
_start:
{
uint8_t v_exclusive_boxed_2814_; lean_object* v_res_2815_; 
v_exclusive_boxed_2814_ = lean_unbox(v_exclusive_2812_);
v_res_2815_ = lean_io_prim_handle_try_lock(v_h_2811_, v_exclusive_boxed_2814_);
lean_dec(v_h_2811_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_unlock___boxed(lean_object* v_h_2818_, lean_object* v_a_00___x40___internal___hyg_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = lean_io_prim_handle_unlock(v_h_2818_);
lean_dec(v_h_2818_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_isTty___boxed(lean_object* v_h_2823_, lean_object* v_a_00___x40___internal___hyg_2824_){
_start:
{
uint8_t v_res_2825_; lean_object* v_r_2826_; 
v_res_2825_ = lean_io_prim_handle_is_tty(v_h_2823_);
lean_dec(v_h_2823_);
v_r_2826_ = lean_box(v_res_2825_);
return v_r_2826_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object* v_h_2829_, lean_object* v_a_00___x40___internal___hyg_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = lean_io_prim_handle_flush(v_h_2829_);
lean_dec(v_h_2829_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_rewind___boxed(lean_object* v_h_2834_, lean_object* v_a_00___x40___internal___hyg_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = lean_io_prim_handle_rewind(v_h_2834_);
lean_dec(v_h_2834_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_truncate___boxed(lean_object* v_h_2839_, lean_object* v_a_00___x40___internal___hyg_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = lean_io_prim_handle_truncate(v_h_2839_);
lean_dec(v_h_2839_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_read___boxed(lean_object* v_h_2845_, lean_object* v_bytes_2846_, lean_object* v_a_00___x40___internal___hyg_2847_){
_start:
{
size_t v_bytes_boxed_2848_; lean_object* v_res_2849_; 
v_bytes_boxed_2848_ = lean_unbox_usize(v_bytes_2846_);
lean_dec(v_bytes_2846_);
v_res_2849_ = lean_io_prim_handle_read(v_h_2845_, v_bytes_boxed_2848_);
lean_dec(v_h_2845_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object* v_h_2853_, lean_object* v_buffer_2854_, lean_object* v_a_00___x40___internal___hyg_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = lean_io_prim_handle_write(v_h_2853_, v_buffer_2854_);
lean_dec_ref(v_buffer_2854_);
lean_dec(v_h_2853_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object* v_h_2859_, lean_object* v_a_00___x40___internal___hyg_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = lean_io_prim_handle_get_line(v_h_2859_);
lean_dec(v_h_2859_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object* v_h_2865_, lean_object* v_s_2866_, lean_object* v_a_00___x40___internal___hyg_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = lean_io_prim_handle_put_str(v_h_2865_, v_s_2866_);
lean_dec_ref(v_s_2866_);
lean_dec(v_h_2865_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object* v_fname_2871_, lean_object* v_a_00___x40___internal___hyg_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = lean_io_realpath(v_fname_2871_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object* v_fname_2876_, lean_object* v_a_00___x40___internal___hyg_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = lean_io_remove_file(v_fname_2876_);
lean_dec_ref(v_fname_2876_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object* v_a_00___x40___internal___hyg_2881_, lean_object* v_a_00___x40___internal___hyg_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = lean_io_remove_dir(v_a_00___x40___internal___hyg_2881_);
lean_dec_ref(v_a_00___x40___internal___hyg_2881_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object* v_a_00___x40___internal___hyg_2886_, lean_object* v_a_00___x40___internal___hyg_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = lean_io_create_dir(v_a_00___x40___internal___hyg_2886_);
lean_dec_ref(v_a_00___x40___internal___hyg_2886_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_rename___boxed(lean_object* v_old_2892_, lean_object* v_new_2893_, lean_object* v_a_00___x40___internal___hyg_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = lean_io_rename(v_old_2892_, v_new_2893_);
lean_dec_ref(v_new_2893_);
lean_dec_ref(v_old_2892_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_hardLink___boxed(lean_object* v_orig_2899_, lean_object* v_link_2900_, lean_object* v_a_00___x40___internal___hyg_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = lean_io_hard_link(v_orig_2899_, v_link_2900_);
lean_dec_ref(v_link_2900_);
lean_dec_ref(v_orig_2899_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createTempFile___boxed(lean_object* v_a_00___x40___internal___hyg_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = lean_io_create_tempfile();
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createTempDir___boxed(lean_object* v_a_00___x40___internal___hyg_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = lean_io_create_tempdir();
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object* v_var_2911_, lean_object* v_a_00___x40___internal___hyg_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = lean_io_getenv(v_var_2911_);
lean_dec_ref(v_var_2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object* v_a_00___x40___internal___hyg_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = lean_io_app_path();
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object* v_a_00___x40___internal___hyg_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = lean_io_current_dir();
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg(lean_object* v_fn_2920_, uint8_t v_mode_2921_, lean_object* v_f_2922_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = lean_io_prim_handle_mk(v_fn_2920_, v_mode_2921_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref(v___x_2924_);
v___x_2926_ = lean_apply_2(v_f_2922_, v_a_2925_, lean_box(0));
return v___x_2926_;
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec_ref(v_f_2922_);
v_a_2927_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2924_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2924_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg___boxed(lean_object* v_fn_2935_, lean_object* v_mode_2936_, lean_object* v_f_2937_, lean_object* v_a_2938_){
_start:
{
uint8_t v_mode_boxed_2939_; lean_object* v_res_2940_; 
v_mode_boxed_2939_ = lean_unbox(v_mode_2936_);
v_res_2940_ = l_IO_FS_withFile___redArg(v_fn_2935_, v_mode_boxed_2939_, v_f_2937_);
lean_dec_ref(v_fn_2935_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object* v_00_u03b1_2941_, lean_object* v_fn_2942_, uint8_t v_mode_2943_, lean_object* v_f_2944_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = lean_io_prim_handle_mk(v_fn_2942_, v_mode_2943_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2948_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref(v___x_2946_);
v___x_2948_ = lean_apply_2(v_f_2944_, v_a_2947_, lean_box(0));
return v___x_2948_;
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v_f_2944_);
v_a_2949_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2946_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2946_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
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
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___boxed(lean_object* v_00_u03b1_2957_, lean_object* v_fn_2958_, lean_object* v_mode_2959_, lean_object* v_f_2960_, lean_object* v_a_2961_){
_start:
{
uint8_t v_mode_boxed_2962_; lean_object* v_res_2963_; 
v_mode_boxed_2962_ = lean_unbox(v_mode_2959_);
v_res_2963_ = l_IO_FS_withFile(v_00_u03b1_2957_, v_fn_2958_, v_mode_boxed_2962_, v_f_2960_);
lean_dec_ref(v_fn_2958_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn(lean_object* v_h_2964_, lean_object* v_s_2965_){
_start:
{
uint32_t v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2967_ = 10;
v___x_2968_ = lean_string_push(v_s_2965_, v___x_2967_);
v___x_2969_ = lean_io_prim_handle_put_str(v_h_2964_, v___x_2968_);
lean_dec_ref(v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object* v_h_2970_, lean_object* v_s_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_IO_FS_Handle_putStrLn(v_h_2970_, v_s_2971_);
lean_dec(v_h_2970_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(lean_object* v_h_2974_, lean_object* v_acc_2975_){
_start:
{
size_t v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = ((size_t)1024ULL);
v___x_2978_ = lean_io_prim_handle_read(v_h_2974_, v___x_2977_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2992_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2981_ = v___x_2978_;
v_isShared_2982_ = v_isSharedCheck_2992_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2978_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2992_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
uint8_t v___x_2983_; 
v___x_2983_ = l_ByteArray_isEmpty(v_a_2979_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_del_object(v___x_2981_);
v___x_2984_ = lean_unsigned_to_nat(0u);
v___x_2985_ = lean_byte_array_size(v_acc_2975_);
v___x_2986_ = lean_byte_array_size(v_a_2979_);
v___x_2987_ = lean_byte_array_copy_slice(v_a_2979_, v___x_2984_, v_acc_2975_, v___x_2985_, v___x_2986_, v___x_2983_);
lean_dec(v_a_2979_);
v_acc_2975_ = v___x_2987_;
goto _start;
}
else
{
lean_object* v___x_2990_; 
lean_dec(v_a_2979_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v_acc_2975_);
v___x_2990_ = v___x_2981_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_acc_2975_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
else
{
lean_dec_ref(v_acc_2975_);
return v___x_2978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop___boxed(lean_object* v_h_2993_, lean_object* v_acc_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_2993_, v_acc_2994_);
lean_dec(v_h_2993_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto(lean_object* v_h_2997_, lean_object* v_buf_2998_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_2997_, v_buf_2998_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto___boxed(lean_object* v_h_3001_, lean_object* v_buf_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_IO_FS_Handle_readBinToEndInto(v_h_3001_, v_buf_3002_);
lean_dec(v_h_3001_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object* v_h_3005_){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = l_ByteArray_empty;
v___x_3008_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_3005_, v___x_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object* v_h_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_IO_FS_Handle_readBinToEnd(v_h_3009_);
lean_dec(v_h_3009_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object* v_h_3015_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_IO_FS_Handle_readBinToEnd(v_h_3015_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3031_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3031_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3031_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
uint8_t v___x_3022_; 
v___x_3022_ = lean_string_validate_utf8(v_a_3018_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
lean_dec(v_a_3018_);
v___x_3023_ = ((lean_object*)(l_IO_FS_Handle_readToEnd___closed__1));
if (v_isShared_3021_ == 0)
{
lean_ctor_set_tag(v___x_3020_, 1);
lean_ctor_set(v___x_3020_, 0, v___x_3023_);
v___x_3025_ = v___x_3020_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3029_; 
v___x_3027_ = lean_string_from_utf8_unchecked(v_a_3018_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v___x_3027_);
v___x_3029_ = v___x_3020_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
v_a_3032_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3017_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3017_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object* v_h_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_IO_FS_Handle_readToEnd(v_h_3040_);
lean_dec(v_h_3040_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read(lean_object* v_h_3043_, lean_object* v_lines_3044_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = lean_io_prim_handle_get_line(v_h_3043_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3102_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3049_ = v___x_3046_;
v_isShared_3050_ = v_isSharedCheck_3102_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3102_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___y_3052_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; uint32_t v___y_3059_; uint32_t v___y_3067_; lean_object* v___x_3089_; lean_object* v___x_3090_; uint8_t v___x_3091_; 
v___x_3089_ = lean_string_length(v_a_3047_);
v___x_3090_ = lean_unsigned_to_nat(0u);
v___x_3091_ = lean_nat_dec_eq(v___x_3089_, v___x_3090_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = lean_string_utf8_byte_size(v_a_3047_);
lean_inc(v_a_3047_);
v___x_3093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3093_, 0, v_a_3047_);
lean_ctor_set(v___x_3093_, 1, v___x_3090_);
lean_ctor_set(v___x_3093_, 2, v___x_3092_);
v___x_3094_ = l_String_Slice_Pos_prev_x3f(v___x_3093_, v___x_3092_);
if (lean_obj_tag(v___x_3094_) == 0)
{
uint32_t v___x_3095_; 
lean_dec_ref(v___x_3093_);
v___x_3095_ = 65;
v___y_3067_ = v___x_3095_;
goto v___jp_3066_;
}
else
{
lean_object* v_val_3096_; lean_object* v___x_3097_; 
v_val_3096_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_val_3096_);
lean_dec_ref(v___x_3094_);
v___x_3097_ = l_String_Slice_Pos_get_x3f(v___x_3093_, v_val_3096_);
lean_dec(v_val_3096_);
lean_dec_ref(v___x_3093_);
if (lean_obj_tag(v___x_3097_) == 0)
{
uint32_t v___x_3098_; 
v___x_3098_ = 65;
v___y_3067_ = v___x_3098_;
goto v___jp_3066_;
}
else
{
lean_object* v_val_3099_; uint32_t v___x_3100_; 
v_val_3099_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_val_3099_);
lean_dec_ref(v___x_3097_);
v___x_3100_ = lean_unbox_uint32(v_val_3099_);
lean_dec(v_val_3099_);
v___y_3067_ = v___x_3100_;
goto v___jp_3066_;
}
}
}
else
{
lean_object* v___x_3101_; 
lean_del_object(v___x_3049_);
lean_dec(v_a_3047_);
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v_lines_3044_);
return v___x_3101_;
}
v___jp_3051_:
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_array_push(v_lines_3044_, v___y_3052_);
v_lines_3044_ = v___x_3053_;
goto _start;
}
v___jp_3055_:
{
uint32_t v___x_3060_; uint8_t v___x_3061_; 
v___x_3060_ = 13;
v___x_3061_ = lean_uint32_dec_eq(v___y_3059_, v___x_3060_);
if (v___x_3061_ == 0)
{
lean_dec(v___y_3058_);
lean_dec(v___y_3056_);
v___y_3052_ = v___y_3057_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3062_ = lean_string_utf8_byte_size(v___y_3057_);
lean_inc(v___y_3056_);
lean_inc_ref(v___y_3057_);
v___x_3063_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3063_, 0, v___y_3057_);
lean_ctor_set(v___x_3063_, 1, v___y_3056_);
lean_ctor_set(v___x_3063_, 2, v___x_3062_);
v___x_3064_ = l_String_Slice_Pos_prevn(v___x_3063_, v___x_3062_, v___y_3058_);
lean_dec_ref(v___x_3063_);
v___x_3065_ = lean_string_utf8_extract(v___y_3057_, v___y_3056_, v___x_3064_);
lean_dec(v___x_3064_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3057_);
v___y_3052_ = v___x_3065_;
goto v___jp_3051_;
}
}
v___jp_3066_:
{
uint32_t v___x_3068_; uint8_t v___x_3069_; 
v___x_3068_ = 10;
v___x_3069_ = lean_uint32_dec_eq(v___y_3067_, v___x_3068_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; lean_object* v___x_3072_; 
v___x_3070_ = lean_array_push(v_lines_3044_, v_a_3047_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v___x_3070_);
v___x_3072_ = v___x_3049_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3070_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
lean_del_object(v___x_3049_);
v___x_3074_ = lean_unsigned_to_nat(1u);
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = lean_string_utf8_byte_size(v_a_3047_);
lean_inc(v_a_3047_);
v___x_3077_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3077_, 0, v_a_3047_);
lean_ctor_set(v___x_3077_, 1, v___x_3075_);
lean_ctor_set(v___x_3077_, 2, v___x_3076_);
v___x_3078_ = l_String_Slice_Pos_prevn(v___x_3077_, v___x_3076_, v___x_3074_);
lean_dec_ref(v___x_3077_);
v___x_3079_ = lean_string_utf8_extract(v_a_3047_, v___x_3075_, v___x_3078_);
lean_dec(v___x_3078_);
lean_dec(v_a_3047_);
v___x_3080_ = lean_string_utf8_byte_size(v___x_3079_);
lean_inc_ref(v___x_3079_);
v___x_3081_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set(v___x_3081_, 1, v___x_3075_);
lean_ctor_set(v___x_3081_, 2, v___x_3080_);
v___x_3082_ = l_String_Slice_Pos_prev_x3f(v___x_3081_, v___x_3080_);
if (lean_obj_tag(v___x_3082_) == 0)
{
uint32_t v___x_3083_; 
lean_dec_ref(v___x_3081_);
v___x_3083_ = 65;
v___y_3056_ = v___x_3075_;
v___y_3057_ = v___x_3079_;
v___y_3058_ = v___x_3074_;
v___y_3059_ = v___x_3083_;
goto v___jp_3055_;
}
else
{
lean_object* v_val_3084_; lean_object* v___x_3085_; 
v_val_3084_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_val_3084_);
lean_dec_ref(v___x_3082_);
v___x_3085_ = l_String_Slice_Pos_get_x3f(v___x_3081_, v_val_3084_);
lean_dec(v_val_3084_);
lean_dec_ref(v___x_3081_);
if (lean_obj_tag(v___x_3085_) == 0)
{
uint32_t v___x_3086_; 
v___x_3086_ = 65;
v___y_3056_ = v___x_3075_;
v___y_3057_ = v___x_3079_;
v___y_3058_ = v___x_3074_;
v___y_3059_ = v___x_3086_;
goto v___jp_3055_;
}
else
{
lean_object* v_val_3087_; uint32_t v___x_3088_; 
v_val_3087_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_val_3087_);
lean_dec_ref(v___x_3085_);
v___x_3088_ = lean_unbox_uint32(v_val_3087_);
lean_dec(v_val_3087_);
v___y_3056_ = v___x_3075_;
v___y_3057_ = v___x_3079_;
v___y_3058_ = v___x_3074_;
v___y_3059_ = v___x_3088_;
goto v___jp_3055_;
}
}
}
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec_ref(v_lines_3044_);
v_a_3103_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3046_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3046_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read___boxed(lean_object* v_h_3111_, lean_object* v_lines_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_3111_, v_lines_3112_);
lean_dec(v_h_3111_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines(lean_object* v_h_3117_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_3120_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_3117_, v___x_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines___boxed(lean_object* v_h_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_IO_FS_Handle_lines(v_h_3121_);
lean_dec(v_h_3121_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object* v_fname_3124_){
_start:
{
uint8_t v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = 0;
v___x_3127_ = lean_io_prim_handle_mk(v_fname_3124_, v___x_3126_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3129_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref(v___x_3127_);
v___x_3129_ = l_IO_FS_Handle_lines(v_a_3128_);
lean_dec(v_a_3128_);
return v___x_3129_;
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
v_a_3130_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3127_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3127_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object* v_fname_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_IO_FS_lines(v_fname_3138_);
lean_dec_ref(v_fname_3138_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object* v_fname_3141_, lean_object* v_content_3142_){
_start:
{
uint8_t v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = 1;
v___x_3145_ = lean_io_prim_handle_mk(v_fname_3141_, v___x_3144_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3147_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3146_);
lean_dec_ref(v___x_3145_);
v___x_3147_ = lean_io_prim_handle_write(v_a_3146_, v_content_3142_);
lean_dec(v_a_3146_);
return v___x_3147_;
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
v_a_3148_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3145_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3145_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object* v_fname_3156_, lean_object* v_content_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_IO_FS_writeBinFile(v_fname_3156_, v_content_3157_);
lean_dec_ref(v_content_3157_);
lean_dec_ref(v_fname_3156_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object* v_fname_3160_, lean_object* v_content_3161_){
_start:
{
uint8_t v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = 1;
v___x_3164_ = lean_io_prim_handle_mk(v_fname_3160_, v___x_3163_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref(v___x_3164_);
v___x_3166_ = lean_io_prim_handle_put_str(v_a_3165_, v_content_3161_);
lean_dec(v_a_3165_);
return v___x_3166_;
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
v_a_3167_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3164_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3164_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object* v_fname_3175_, lean_object* v_content_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_IO_FS_writeFile(v_fname_3175_, v_content_3176_);
lean_dec_ref(v_content_3176_);
lean_dec_ref(v_fname_3175_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object* v_strm_3179_, lean_object* v_s_3180_){
_start:
{
lean_object* v_putStr_3182_; uint32_t v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v_putStr_3182_ = lean_ctor_get(v_strm_3179_, 4);
lean_inc_ref(v_putStr_3182_);
lean_dec_ref(v_strm_3179_);
v___x_3183_ = 10;
v___x_3184_ = lean_string_push(v_s_3180_, v___x_3183_);
v___x_3185_ = lean_apply_2(v_putStr_3182_, v___x_3184_, lean_box(0));
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn___boxed(lean_object* v_strm_3186_, lean_object* v_s_3187_, lean_object* v_a_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_IO_FS_Stream_putStrLn(v_strm_3186_, v_s_3187_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00IO_FS_instReprDirEntry_repr_spec__0(lean_object* v_a_3190_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_nat_to_int(v_a_3190_);
return v___x_3191_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = lean_unsigned_to_nat(8u);
v___x_3206_ = lean_nat_to_int(v___x_3205_);
return v___x_3206_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = lean_unsigned_to_nat(12u);
v___x_3217_ = lean_nat_to_int(v___x_3216_);
return v___x_3217_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__0));
v___x_3220_ = lean_string_length(v___x_3219_);
return v___x_3220_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__16, &l_IO_FS_instReprDirEntry_repr___redArg___closed__16_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16);
v___x_3222_ = lean_nat_to_int(v___x_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___redArg(lean_object* v_x_3227_){
_start:
{
lean_object* v_root_3228_; lean_object* v_fileName_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3268_; 
v_root_3228_ = lean_ctor_get(v_x_3227_, 0);
v_fileName_3229_ = lean_ctor_get(v_x_3227_, 1);
v_isSharedCheck_3268_ = !lean_is_exclusive(v_x_3227_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3231_ = v_x_3227_;
v_isShared_3232_ = v_isSharedCheck_3268_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_fileName_3229_);
lean_inc(v_root_3228_);
lean_dec(v_x_3227_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3268_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3233_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3234_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__6));
v___x_3235_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3236_ = lean_unsigned_to_nat(0u);
v___x_3237_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__9));
v___x_3238_ = l_String_quote(v_root_3228_);
v___x_3239_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set_tag(v___x_3231_, 5);
lean_ctor_set(v___x_3231_, 1, v___x_3239_);
lean_ctor_set(v___x_3231_, 0, v___x_3237_);
v___x_3241_ = v___x_3231_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3237_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3242_ = l_Repr_addAppParen(v___x_3241_, v___x_3236_);
v___x_3243_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3235_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = 0;
v___x_3245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set_uint8(v___x_3245_, sizeof(void*)*1, v___x_3244_);
v___x_3246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3234_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_box(1);
v___x_3250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3248_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__13));
v___x_3252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
lean_ctor_set(v___x_3253_, 1, v___x_3233_);
v___x_3254_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__14, &l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14);
v___x_3255_ = l_String_quote(v_fileName_3229_);
v___x_3256_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
v___x_3257_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3254_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
lean_ctor_set_uint8(v___x_3258_, sizeof(void*)*1, v___x_3244_);
v___x_3259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3253_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3261_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set(v___x_3262_, 1, v___x_3259_);
v___x_3263_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3262_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3260_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
v___x_3266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
lean_ctor_set_uint8(v___x_3266_, sizeof(void*)*1, v___x_3244_);
return v___x_3266_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr(lean_object* v_x_3269_, lean_object* v_prec_3270_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_IO_FS_instReprDirEntry_repr___redArg(v_x_3269_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___boxed(lean_object* v_x_3272_, lean_object* v_prec_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_IO_FS_instReprDirEntry_repr(v_x_3272_, v_prec_3273_);
lean_dec(v_prec_3273_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object* v_entry_3277_){
_start:
{
lean_object* v_root_3278_; lean_object* v_fileName_3279_; lean_object* v___x_3280_; 
v_root_3278_ = lean_ctor_get(v_entry_3277_, 0);
lean_inc_ref(v_root_3278_);
v_fileName_3279_ = lean_ctor_get(v_entry_3277_, 1);
lean_inc_ref(v_fileName_3279_);
lean_dec_ref(v_entry_3277_);
v___x_3280_ = l_System_FilePath_join(v_root_3278_, v_fileName_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx(uint8_t v_x_3281_){
_start:
{
switch(v_x_3281_)
{
case 0:
{
lean_object* v___x_3282_; 
v___x_3282_ = lean_unsigned_to_nat(0u);
return v___x_3282_;
}
case 1:
{
lean_object* v___x_3283_; 
v___x_3283_ = lean_unsigned_to_nat(1u);
return v___x_3283_;
}
case 2:
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_unsigned_to_nat(2u);
return v___x_3284_;
}
default: 
{
lean_object* v___x_3285_; 
v___x_3285_ = lean_unsigned_to_nat(3u);
return v___x_3285_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx___boxed(lean_object* v_x_3286_){
_start:
{
uint8_t v_x_boxed_3287_; lean_object* v_res_3288_; 
v_x_boxed_3287_ = lean_unbox(v_x_3286_);
v_res_3288_ = l_IO_FS_FileType_ctorIdx(v_x_boxed_3287_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx(uint8_t v_x_3289_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_IO_FS_FileType_ctorIdx(v_x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx___boxed(lean_object* v_x_3291_){
_start:
{
uint8_t v_x_4__boxed_3292_; lean_object* v_res_3293_; 
v_x_4__boxed_3292_ = lean_unbox(v_x_3291_);
v_res_3293_ = l_IO_FS_FileType_toCtorIdx(v_x_4__boxed_3292_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg(lean_object* v_k_3294_){
_start:
{
lean_inc(v_k_3294_);
return v_k_3294_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg___boxed(lean_object* v_k_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_IO_FS_FileType_ctorElim___redArg(v_k_3295_);
lean_dec(v_k_3295_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim(lean_object* v_motive_3297_, lean_object* v_ctorIdx_3298_, uint8_t v_t_3299_, lean_object* v_h_3300_, lean_object* v_k_3301_){
_start:
{
lean_inc(v_k_3301_);
return v_k_3301_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___boxed(lean_object* v_motive_3302_, lean_object* v_ctorIdx_3303_, lean_object* v_t_3304_, lean_object* v_h_3305_, lean_object* v_k_3306_){
_start:
{
uint8_t v_t_boxed_3307_; lean_object* v_res_3308_; 
v_t_boxed_3307_ = lean_unbox(v_t_3304_);
v_res_3308_ = l_IO_FS_FileType_ctorElim(v_motive_3302_, v_ctorIdx_3303_, v_t_boxed_3307_, v_h_3305_, v_k_3306_);
lean_dec(v_k_3306_);
lean_dec(v_ctorIdx_3303_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg(lean_object* v_dir_3309_){
_start:
{
lean_inc(v_dir_3309_);
return v_dir_3309_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg___boxed(lean_object* v_dir_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_IO_FS_FileType_dir_elim___redArg(v_dir_3310_);
lean_dec(v_dir_3310_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim(lean_object* v_motive_3312_, uint8_t v_t_3313_, lean_object* v_h_3314_, lean_object* v_dir_3315_){
_start:
{
lean_inc(v_dir_3315_);
return v_dir_3315_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___boxed(lean_object* v_motive_3316_, lean_object* v_t_3317_, lean_object* v_h_3318_, lean_object* v_dir_3319_){
_start:
{
uint8_t v_t_boxed_3320_; lean_object* v_res_3321_; 
v_t_boxed_3320_ = lean_unbox(v_t_3317_);
v_res_3321_ = l_IO_FS_FileType_dir_elim(v_motive_3316_, v_t_boxed_3320_, v_h_3318_, v_dir_3319_);
lean_dec(v_dir_3319_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg(lean_object* v_file_3322_){
_start:
{
lean_inc(v_file_3322_);
return v_file_3322_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg___boxed(lean_object* v_file_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_IO_FS_FileType_file_elim___redArg(v_file_3323_);
lean_dec(v_file_3323_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim(lean_object* v_motive_3325_, uint8_t v_t_3326_, lean_object* v_h_3327_, lean_object* v_file_3328_){
_start:
{
lean_inc(v_file_3328_);
return v_file_3328_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___boxed(lean_object* v_motive_3329_, lean_object* v_t_3330_, lean_object* v_h_3331_, lean_object* v_file_3332_){
_start:
{
uint8_t v_t_boxed_3333_; lean_object* v_res_3334_; 
v_t_boxed_3333_ = lean_unbox(v_t_3330_);
v_res_3334_ = l_IO_FS_FileType_file_elim(v_motive_3329_, v_t_boxed_3333_, v_h_3331_, v_file_3332_);
lean_dec(v_file_3332_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg(lean_object* v_symlink_3335_){
_start:
{
lean_inc(v_symlink_3335_);
return v_symlink_3335_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg___boxed(lean_object* v_symlink_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_IO_FS_FileType_symlink_elim___redArg(v_symlink_3336_);
lean_dec(v_symlink_3336_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim(lean_object* v_motive_3338_, uint8_t v_t_3339_, lean_object* v_h_3340_, lean_object* v_symlink_3341_){
_start:
{
lean_inc(v_symlink_3341_);
return v_symlink_3341_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___boxed(lean_object* v_motive_3342_, lean_object* v_t_3343_, lean_object* v_h_3344_, lean_object* v_symlink_3345_){
_start:
{
uint8_t v_t_boxed_3346_; lean_object* v_res_3347_; 
v_t_boxed_3346_ = lean_unbox(v_t_3343_);
v_res_3347_ = l_IO_FS_FileType_symlink_elim(v_motive_3342_, v_t_boxed_3346_, v_h_3344_, v_symlink_3345_);
lean_dec(v_symlink_3345_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg(lean_object* v_other_3348_){
_start:
{
lean_inc(v_other_3348_);
return v_other_3348_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg___boxed(lean_object* v_other_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_IO_FS_FileType_other_elim___redArg(v_other_3349_);
lean_dec(v_other_3349_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim(lean_object* v_motive_3351_, uint8_t v_t_3352_, lean_object* v_h_3353_, lean_object* v_other_3354_){
_start:
{
lean_inc(v_other_3354_);
return v_other_3354_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___boxed(lean_object* v_motive_3355_, lean_object* v_t_3356_, lean_object* v_h_3357_, lean_object* v_other_3358_){
_start:
{
uint8_t v_t_boxed_3359_; lean_object* v_res_3360_; 
v_t_boxed_3359_ = lean_unbox(v_t_3356_);
v_res_3360_ = l_IO_FS_FileType_other_elim(v_motive_3355_, v_t_boxed_3359_, v_h_3357_, v_other_3358_);
lean_dec(v_other_3358_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr(uint8_t v_x_3373_, lean_object* v_prec_3374_){
_start:
{
lean_object* v___y_3376_; lean_object* v___y_3383_; lean_object* v___y_3390_; lean_object* v___y_3397_; 
switch(v_x_3373_)
{
case 0:
{
lean_object* v___x_3403_; uint8_t v___x_3404_; 
v___x_3403_ = lean_unsigned_to_nat(1024u);
v___x_3404_ = lean_nat_dec_le(v___x_3403_, v_prec_3374_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3376_ = v___x_3405_;
goto v___jp_3375_;
}
else
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3376_ = v___x_3406_;
goto v___jp_3375_;
}
}
case 1:
{
lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3407_ = lean_unsigned_to_nat(1024u);
v___x_3408_ = lean_nat_dec_le(v___x_3407_, v_prec_3374_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; 
v___x_3409_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3383_ = v___x_3409_;
goto v___jp_3382_;
}
else
{
lean_object* v___x_3410_; 
v___x_3410_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3383_ = v___x_3410_;
goto v___jp_3382_;
}
}
case 2:
{
lean_object* v___x_3411_; uint8_t v___x_3412_; 
v___x_3411_ = lean_unsigned_to_nat(1024u);
v___x_3412_ = lean_nat_dec_le(v___x_3411_, v_prec_3374_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3390_ = v___x_3413_;
goto v___jp_3389_;
}
else
{
lean_object* v___x_3414_; 
v___x_3414_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3390_ = v___x_3414_;
goto v___jp_3389_;
}
}
default: 
{
lean_object* v___x_3415_; uint8_t v___x_3416_; 
v___x_3415_ = lean_unsigned_to_nat(1024u);
v___x_3416_ = lean_nat_dec_le(v___x_3415_, v_prec_3374_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3397_ = v___x_3417_;
goto v___jp_3396_;
}
else
{
lean_object* v___x_3418_; 
v___x_3418_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3397_ = v___x_3418_;
goto v___jp_3396_;
}
}
}
v___jp_3375_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3377_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__1));
lean_inc(v___y_3376_);
v___x_3378_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___y_3376_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = 0;
v___x_3380_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3380_, 0, v___x_3378_);
lean_ctor_set_uint8(v___x_3380_, sizeof(void*)*1, v___x_3379_);
v___x_3381_ = l_Repr_addAppParen(v___x_3380_, v_prec_3374_);
return v___x_3381_;
}
v___jp_3382_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3384_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__3));
lean_inc(v___y_3383_);
v___x_3385_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___y_3383_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = 0;
v___x_3387_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3387_, 0, v___x_3385_);
lean_ctor_set_uint8(v___x_3387_, sizeof(void*)*1, v___x_3386_);
v___x_3388_ = l_Repr_addAppParen(v___x_3387_, v_prec_3374_);
return v___x_3388_;
}
v___jp_3389_:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3391_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__5));
lean_inc(v___y_3390_);
v___x_3392_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___y_3390_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = 0;
v___x_3394_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3394_, 0, v___x_3392_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*1, v___x_3393_);
v___x_3395_ = l_Repr_addAppParen(v___x_3394_, v_prec_3374_);
return v___x_3395_;
}
v___jp_3396_:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; uint8_t v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3398_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__7));
lean_inc(v___y_3397_);
v___x_3399_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___y_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = 0;
v___x_3401_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set_uint8(v___x_3401_, sizeof(void*)*1, v___x_3400_);
v___x_3402_ = l_Repr_addAppParen(v___x_3401_, v_prec_3374_);
return v___x_3402_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr___boxed(lean_object* v_x_3419_, lean_object* v_prec_3420_){
_start:
{
uint8_t v_x_229__boxed_3421_; lean_object* v_res_3422_; 
v_x_229__boxed_3421_ = lean_unbox(v_x_3419_);
v_res_3422_ = l_IO_FS_instReprFileType_repr(v_x_229__boxed_3421_, v_prec_3420_);
lean_dec(v_prec_3420_);
return v_res_3422_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instBEqFileType_beq(uint8_t v_x_3425_, uint8_t v_y_3426_){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
v___x_3427_ = l_IO_FS_FileType_ctorIdx(v_x_3425_);
v___x_3428_ = l_IO_FS_FileType_ctorIdx(v_y_3426_);
v___x_3429_ = lean_nat_dec_eq(v___x_3427_, v___x_3428_);
lean_dec(v___x_3428_);
lean_dec(v___x_3427_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType_beq___boxed(lean_object* v_x_3430_, lean_object* v_y_3431_){
_start:
{
uint8_t v_x_17__boxed_3432_; uint8_t v_y_18__boxed_3433_; uint8_t v_res_3434_; lean_object* v_r_3435_; 
v_x_17__boxed_3432_ = lean_unbox(v_x_3430_);
v_y_18__boxed_3433_ = lean_unbox(v_y_3431_);
v_res_3434_ = l_IO_FS_instBEqFileType_beq(v_x_17__boxed_3432_, v_y_18__boxed_3433_);
v_r_3435_ = lean_box(v_res_3434_);
return v_r_3435_;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3447_ = lean_unsigned_to_nat(7u);
v___x_3448_ = lean_nat_to_int(v___x_3447_);
return v___x_3448_;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3452_ = lean_unsigned_to_nat(0u);
v___x_3453_ = lean_nat_to_int(v___x_3452_);
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object* v_x_3454_){
_start:
{
lean_object* v_sec_3455_; uint32_t v_nsec_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___y_3461_; lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; 
v_sec_3455_ = lean_ctor_get(v_x_3454_, 0);
v_nsec_3456_ = lean_ctor_get_uint32(v_x_3454_, sizeof(void*)*1);
v___x_3457_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3458_ = ((lean_object*)(l_IO_FS_instReprSystemTime_repr___redArg___closed__3));
v___x_3459_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__4, &l_IO_FS_instReprSystemTime_repr___redArg___closed__4_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4);
v___x_3487_ = lean_unsigned_to_nat(0u);
v___x_3488_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__7, &l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7);
v___x_3489_ = lean_int_dec_lt(v_sec_3455_, v___x_3488_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = l_Int_repr(v_sec_3455_);
v___x_3491_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
v___y_3461_ = v___x_3491_;
goto v___jp_3460_;
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3492_ = l_Int_repr(v_sec_3455_);
v___x_3493_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
v___x_3494_ = l_Repr_addAppParen(v___x_3493_, v___x_3487_);
v___y_3461_ = v___x_3494_;
goto v___jp_3460_;
}
v___jp_3460_:
{
lean_object* v___x_3462_; uint8_t v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3462_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3459_);
lean_ctor_set(v___x_3462_, 1, v___y_3461_);
v___x_3463_ = 0;
v___x_3464_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3464_, 0, v___x_3462_);
lean_ctor_set_uint8(v___x_3464_, sizeof(void*)*1, v___x_3463_);
v___x_3465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3458_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
v___x_3466_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3465_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
v___x_3468_ = lean_box(1);
v___x_3469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3467_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = ((lean_object*)(l_IO_FS_instReprSystemTime_repr___redArg___closed__6));
v___x_3471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3469_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
lean_ctor_set(v___x_3472_, 1, v___x_3457_);
v___x_3473_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3474_ = lean_uint32_to_nat(v_nsec_3456_);
v___x_3475_ = l_Nat_reprFast(v___x_3474_);
v___x_3476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
v___x_3477_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3473_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v___x_3478_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
lean_ctor_set_uint8(v___x_3478_, sizeof(void*)*1, v___x_3463_);
v___x_3479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3472_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
v___x_3480_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3481_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3482_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
lean_ctor_set(v___x_3482_, 1, v___x_3479_);
v___x_3483_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3484_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3482_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
v___x_3485_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3480_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_ctor_set_uint8(v___x_3486_, sizeof(void*)*1, v___x_3463_);
return v___x_3486_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg___boxed(lean_object* v_x_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_3495_);
lean_dec_ref(v_x_3495_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr(lean_object* v_x_3497_, lean_object* v_prec_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_3497_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___boxed(lean_object* v_x_3500_, lean_object* v_prec_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l_IO_FS_instReprSystemTime_repr(v_x_3500_, v_prec_3501_);
lean_dec(v_prec_3501_);
lean_dec_ref(v_x_3500_);
return v_res_3502_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instBEqSystemTime_beq(lean_object* v_x_3505_, lean_object* v_x_3506_){
_start:
{
lean_object* v_sec_3507_; uint32_t v_nsec_3508_; lean_object* v_sec_3509_; uint32_t v_nsec_3510_; uint8_t v___x_3511_; 
v_sec_3507_ = lean_ctor_get(v_x_3505_, 0);
v_nsec_3508_ = lean_ctor_get_uint32(v_x_3505_, sizeof(void*)*1);
v_sec_3509_ = lean_ctor_get(v_x_3506_, 0);
v_nsec_3510_ = lean_ctor_get_uint32(v_x_3506_, sizeof(void*)*1);
v___x_3511_ = lean_int_dec_eq(v_sec_3507_, v_sec_3509_);
if (v___x_3511_ == 0)
{
return v___x_3511_;
}
else
{
uint8_t v___x_3512_; 
v___x_3512_ = lean_uint32_dec_eq(v_nsec_3508_, v_nsec_3510_);
return v___x_3512_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime_beq___boxed(lean_object* v_x_3513_, lean_object* v_x_3514_){
_start:
{
uint8_t v_res_3515_; lean_object* v_r_3516_; 
v_res_3515_ = l_IO_FS_instBEqSystemTime_beq(v_x_3513_, v_x_3514_);
lean_dec_ref(v_x_3514_);
lean_dec_ref(v_x_3513_);
v_r_3516_ = lean_box(v_res_3515_);
return v_r_3516_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object* v_x_3519_, lean_object* v_x_3520_){
_start:
{
lean_object* v_sec_3521_; uint32_t v_nsec_3522_; lean_object* v_sec_3523_; uint32_t v_nsec_3524_; uint8_t v___x_3525_; 
v_sec_3521_ = lean_ctor_get(v_x_3519_, 0);
v_nsec_3522_ = lean_ctor_get_uint32(v_x_3519_, sizeof(void*)*1);
v_sec_3523_ = lean_ctor_get(v_x_3520_, 0);
v_nsec_3524_ = lean_ctor_get_uint32(v_x_3520_, sizeof(void*)*1);
v___x_3525_ = lean_int_dec_lt(v_sec_3521_, v_sec_3523_);
if (v___x_3525_ == 0)
{
uint8_t v___x_3526_; 
v___x_3526_ = lean_int_dec_eq(v_sec_3521_, v_sec_3523_);
if (v___x_3526_ == 0)
{
uint8_t v___x_3527_; 
v___x_3527_ = 2;
return v___x_3527_;
}
else
{
uint8_t v___x_3528_; 
v___x_3528_ = lean_uint32_dec_lt(v_nsec_3522_, v_nsec_3524_);
if (v___x_3528_ == 0)
{
uint8_t v___x_3529_; 
v___x_3529_ = lean_uint32_dec_eq(v_nsec_3522_, v_nsec_3524_);
if (v___x_3529_ == 0)
{
uint8_t v___x_3530_; 
v___x_3530_ = 2;
return v___x_3530_;
}
else
{
uint8_t v___x_3531_; 
v___x_3531_ = 1;
return v___x_3531_;
}
}
else
{
uint8_t v___x_3532_; 
v___x_3532_ = 0;
return v___x_3532_;
}
}
}
else
{
uint8_t v___x_3533_; 
v___x_3533_ = 0;
return v___x_3533_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime_ord___boxed(lean_object* v_x_3534_, lean_object* v_x_3535_){
_start:
{
uint8_t v_res_3536_; lean_object* v_r_3537_; 
v_res_3536_ = l_IO_FS_instOrdSystemTime_ord(v_x_3534_, v_x_3535_);
lean_dec_ref(v_x_3535_);
lean_dec_ref(v_x_3534_);
v_r_3537_ = lean_box(v_res_3536_);
return v_r_3537_;
}
}
static uint32_t _init_l_IO_FS_instInhabitedSystemTime_default___closed__0(void){
_start:
{
lean_object* v___x_3540_; uint32_t v___x_3541_; 
v___x_3540_ = lean_unsigned_to_nat(0u);
v___x_3541_ = lean_uint32_of_nat(v___x_3540_);
return v___x_3541_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default___closed__1(void){
_start:
{
uint32_t v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3542_ = lean_uint32_once(&l_IO_FS_instInhabitedSystemTime_default___closed__0, &l_IO_FS_instInhabitedSystemTime_default___closed__0_once, _init_l_IO_FS_instInhabitedSystemTime_default___closed__0);
v___x_3543_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__7, &l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7);
v___x_3544_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
lean_ctor_set_uint32(v___x_3544_, sizeof(void*)*1, v___x_3542_);
return v___x_3544_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default(void){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = lean_obj_once(&l_IO_FS_instInhabitedSystemTime_default___closed__1, &l_IO_FS_instInhabitedSystemTime_default___closed__1_once, _init_l_IO_FS_instInhabitedSystemTime_default___closed__1);
return v___x_3545_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime(void){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_IO_FS_instInhabitedSystemTime_default;
return v___x_3546_;
}
}
static lean_object* _init_l_IO_FS_instLTSystemTime(void){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = lean_box(0);
return v___x_3547_;
}
}
static lean_object* _init_l_IO_FS_instLESystemTime(void){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = lean_box(0);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg(lean_object* v_x_3570_){
_start:
{
lean_object* v_accessed_3571_; lean_object* v_modified_3572_; uint64_t v_byteSize_3573_; uint8_t v_type_3574_; uint64_t v_numLinks_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v_accessed_3571_ = lean_ctor_get(v_x_3570_, 0);
v_modified_3572_ = lean_ctor_get(v_x_3570_, 1);
v_byteSize_3573_ = lean_ctor_get_uint64(v_x_3570_, sizeof(void*)*2);
v_type_3574_ = lean_ctor_get_uint8(v_x_3570_, sizeof(void*)*2 + 16);
v_numLinks_3575_ = lean_ctor_get_uint64(v_x_3570_, sizeof(void*)*2 + 8);
v___x_3576_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3577_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__3));
v___x_3578_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__14, &l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14);
v___x_3579_ = lean_unsigned_to_nat(0u);
v___x_3580_ = l_IO_FS_instReprSystemTime_repr___redArg(v_accessed_3571_);
v___x_3581_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3578_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = 0;
v___x_3583_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3583_, 0, v___x_3581_);
lean_ctor_set_uint8(v___x_3583_, sizeof(void*)*1, v___x_3582_);
v___x_3584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3577_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3584_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = lean_box(1);
v___x_3588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3586_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
v___x_3589_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__5));
v___x_3590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3588_);
lean_ctor_set(v___x_3590_, 1, v___x_3589_);
v___x_3591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3590_);
lean_ctor_set(v___x_3591_, 1, v___x_3576_);
v___x_3592_ = l_IO_FS_instReprSystemTime_repr___redArg(v_modified_3572_);
v___x_3593_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3578_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
v___x_3594_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
lean_ctor_set_uint8(v___x_3594_, sizeof(void*)*1, v___x_3582_);
v___x_3595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3591_);
lean_ctor_set(v___x_3595_, 1, v___x_3594_);
v___x_3596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
lean_ctor_set(v___x_3596_, 1, v___x_3585_);
v___x_3597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
lean_ctor_set(v___x_3597_, 1, v___x_3587_);
v___x_3598_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__7));
v___x_3599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3597_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
lean_ctor_set(v___x_3600_, 1, v___x_3576_);
v___x_3601_ = lean_uint64_to_nat(v_byteSize_3573_);
v___x_3602_ = l_Nat_reprFast(v___x_3601_);
v___x_3603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
v___x_3604_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3578_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3605_, 0, v___x_3604_);
lean_ctor_set_uint8(v___x_3605_, sizeof(void*)*1, v___x_3582_);
v___x_3606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3600_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
lean_ctor_set(v___x_3607_, 1, v___x_3585_);
v___x_3608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set(v___x_3608_, 1, v___x_3587_);
v___x_3609_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__9));
v___x_3610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3608_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3610_);
lean_ctor_set(v___x_3611_, 1, v___x_3576_);
v___x_3612_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3613_ = l_IO_FS_instReprFileType_repr(v_type_3574_, v___x_3579_);
v___x_3614_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3612_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
lean_ctor_set_uint8(v___x_3615_, sizeof(void*)*1, v___x_3582_);
v___x_3616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3611_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
v___x_3617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
lean_ctor_set(v___x_3617_, 1, v___x_3585_);
v___x_3618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
lean_ctor_set(v___x_3618_, 1, v___x_3587_);
v___x_3619_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__11));
v___x_3620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
lean_ctor_set(v___x_3621_, 1, v___x_3576_);
v___x_3622_ = lean_uint64_to_nat(v_numLinks_3575_);
v___x_3623_ = l_Nat_reprFast(v___x_3622_);
v___x_3624_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
v___x_3625_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3578_);
lean_ctor_set(v___x_3625_, 1, v___x_3624_);
v___x_3626_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
lean_ctor_set_uint8(v___x_3626_, sizeof(void*)*1, v___x_3582_);
v___x_3627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3621_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3629_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3629_);
lean_ctor_set(v___x_3630_, 1, v___x_3627_);
v___x_3631_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3630_);
lean_ctor_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3628_);
lean_ctor_set(v___x_3633_, 1, v___x_3632_);
v___x_3634_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
lean_ctor_set_uint8(v___x_3634_, sizeof(void*)*1, v___x_3582_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg___boxed(lean_object* v_x_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_3635_);
lean_dec_ref(v_x_3635_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr(lean_object* v_x_3637_, lean_object* v_prec_3638_){
_start:
{
lean_object* v___x_3639_; 
v___x_3639_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_3637_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___boxed(lean_object* v_x_3640_, lean_object* v_prec_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_IO_FS_instReprMetadata_repr(v_x_3640_, v_prec_3641_);
lean_dec(v_prec_3641_);
lean_dec_ref(v_x_3640_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object* v_a_00___x40___internal___hyg_3647_, lean_object* v_a_00___x40___internal___hyg_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = lean_io_read_dir(v_a_00___x40___internal___hyg_3647_);
lean_dec_ref(v_a_00___x40___internal___hyg_3647_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object* v_a_00___x40___internal___hyg_3652_, lean_object* v_a_00___x40___internal___hyg_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = lean_io_metadata(v_a_00___x40___internal___hyg_3652_);
lean_dec_ref(v_a_00___x40___internal___hyg_3652_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_symlinkMetadata___boxed(lean_object* v_a_00___x40___internal___hyg_3657_, lean_object* v_a_00___x40___internal___hyg_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = lean_io_symlink_metadata(v_a_00___x40___internal___hyg_3657_);
lean_dec_ref(v_a_00___x40___internal___hyg_3657_);
return v_res_3659_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isDir(lean_object* v_p_3660_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = lean_io_metadata(v_p_3660_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; uint8_t v_type_3664_; uint8_t v___x_3665_; uint8_t v___x_3666_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref(v___x_3662_);
v_type_3664_ = lean_ctor_get_uint8(v_a_3663_, sizeof(void*)*2 + 16);
lean_dec(v_a_3663_);
v___x_3665_ = 0;
v___x_3666_ = l_IO_FS_instBEqFileType_beq(v_type_3664_, v___x_3665_);
return v___x_3666_;
}
else
{
uint8_t v___x_3667_; 
lean_dec_ref(v___x_3662_);
v___x_3667_ = 0;
return v___x_3667_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object* v_p_3668_, lean_object* v_a_3669_){
_start:
{
uint8_t v_res_3670_; lean_object* v_r_3671_; 
v_res_3670_ = l_System_FilePath_isDir(v_p_3668_);
lean_dec_ref(v_p_3668_);
v_r_3671_ = lean_box(v_res_3670_);
return v_r_3671_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_pathExists(lean_object* v_p_3672_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = lean_io_metadata(v_p_3672_);
if (lean_obj_tag(v___x_3674_) == 0)
{
uint8_t v___x_3675_; 
lean_dec_ref(v___x_3674_);
v___x_3675_ = 1;
return v___x_3675_;
}
else
{
uint8_t v___x_3676_; 
lean_dec_ref(v___x_3674_);
v___x_3676_ = 0;
return v___x_3676_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object* v_p_3677_, lean_object* v_a_3678_){
_start:
{
uint8_t v_res_3679_; lean_object* v_r_3680_; 
v_res_3679_ = l_System_FilePath_pathExists(v_p_3677_);
lean_dec_ref(v_p_3677_);
v_r_3680_ = lean_box(v_res_3679_);
return v_r_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(lean_object* v_enter_3681_, lean_object* v_p_3682_, lean_object* v_as_3683_, size_t v_sz_3684_, size_t v_i_3685_, lean_object* v_b_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v_a_3690_; lean_object* v_snd_3691_; uint8_t v___x_3695_; 
v___x_3695_ = lean_usize_dec_lt(v_i_3685_, v_sz_3684_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
lean_dec_ref(v_p_3682_);
lean_dec_ref(v_enter_3681_);
v___x_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3696_, 0, v_b_3686_);
lean_ctor_set(v___x_3696_, 1, v___y_3687_);
v___x_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
return v___x_3697_;
}
else
{
lean_object* v___x_3698_; lean_object* v_a_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3698_ = lean_box(0);
v_a_3699_ = lean_array_uget_borrowed(v_as_3683_, v_i_3685_);
lean_inc(v_a_3699_);
v___x_3700_ = l_IO_FS_DirEntry_path(v_a_3699_);
lean_inc_ref(v___x_3700_);
v___x_3701_ = lean_array_push(v___y_3687_, v___x_3700_);
v___x_3702_ = lean_io_metadata(v___x_3700_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; uint8_t v_type_3704_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_a_3703_);
lean_dec_ref(v___x_3702_);
v_type_3704_ = lean_ctor_get_uint8(v_a_3703_, sizeof(void*)*2 + 16);
lean_dec(v_a_3703_);
switch(v_type_3704_)
{
case 2:
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_io_realpath(v___x_3700_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; uint8_t v___x_3707_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref(v___x_3705_);
v___x_3707_ = l_System_FilePath_isDir(v_a_3706_);
if (v___x_3707_ == 0)
{
lean_dec(v_a_3706_);
v_a_3690_ = v___x_3698_;
v_snd_3691_ = v___x_3701_;
goto v___jp_3689_;
}
else
{
lean_object* v___x_3708_; 
lean_inc_ref(v_enter_3681_);
lean_inc_ref(v_p_3682_);
v___x_3708_ = lean_apply_2(v_enter_3681_, v_p_3682_, lean_box(0));
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; uint8_t v___x_3710_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref(v___x_3708_);
v___x_3710_ = lean_unbox(v_a_3709_);
lean_dec(v_a_3709_);
if (v___x_3710_ == 0)
{
lean_dec(v_a_3706_);
v_a_3690_ = v___x_3698_;
v_snd_3691_ = v___x_3701_;
goto v___jp_3689_;
}
else
{
lean_object* v___x_3711_; 
lean_inc_ref(v_enter_3681_);
v___x_3711_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3681_, v_a_3706_, v___x_3701_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v_snd_3713_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref(v___x_3711_);
v_snd_3713_ = lean_ctor_get(v_a_3712_, 1);
lean_inc(v_snd_3713_);
lean_dec(v_a_3712_);
v_a_3690_ = v___x_3698_;
v_snd_3691_ = v_snd_3713_;
goto v___jp_3689_;
}
else
{
lean_dec_ref(v_p_3682_);
lean_dec_ref(v_enter_3681_);
return v___x_3711_;
}
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
lean_dec(v_a_3706_);
lean_dec_ref(v___x_3701_);
lean_dec_ref(v_p_3682_);
lean_dec_ref(v_enter_3681_);
v_a_3714_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___x_3708_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3708_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec_ref(v___x_3701_);
lean_dec_ref(v_p_3682_);
lean_dec_ref(v_enter_3681_);
v_a_3722_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3705_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3705_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
case 0:
{
lean_object* v___x_3730_; 
lean_inc_ref(v_enter_3681_);
v___x_3730_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3681_, v___x_3700_, v___x_3701_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v_snd_3732_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
lean_dec_ref(v___x_3730_);
v_snd_3732_ = lean_ctor_get(v_a_3731_, 1);
lean_inc(v_snd_3732_);
lean_dec(v_a_3731_);
v_a_3690_ = v___x_3698_;
v_snd_3691_ = v_snd_3732_;
goto v___jp_3689_;
}
else
{
lean_dec_ref(v_p_3682_);
lean_dec_ref(v_enter_3681_);
return v___x_3730_;
}
}
default: 
{
lean_dec_ref(v___x_3700_);
v_a_3690_ = v___x_3698_;
v_snd_3691_ = v___x_3701_;
goto v___jp_3689_;
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec_ref(v___x_3700_);
v_a_3733_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3702_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3702_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
if (lean_obj_tag(v_a_3733_) == 11)
{
lean_dec_ref(v_a_3733_);
lean_del_object(v___x_3735_);
v_a_3690_ = v___x_3698_;
v_snd_3691_ = v___x_3701_;
goto v___jp_3689_;
}
else
{
lean_object* v___x_3738_; 
lean_dec_ref(v___x_3701_);
lean_dec_ref(v_p_3682_);
lean_dec_ref(v_enter_3681_);
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
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
v___jp_3689_:
{
size_t v___x_3692_; size_t v___x_3693_; 
v___x_3692_ = ((size_t)1ULL);
v___x_3693_ = lean_usize_add(v_i_3685_, v___x_3692_);
v_i_3685_ = v___x_3693_;
v_b_3686_ = v_a_3690_;
v___y_3687_ = v_snd_3691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go(lean_object* v_enter_3741_, lean_object* v_p_3742_, lean_object* v_a_3743_){
_start:
{
lean_object* v___x_3745_; 
lean_inc_ref(v_enter_3741_);
lean_inc_ref(v_p_3742_);
v___x_3745_ = lean_apply_2(v_enter_3741_, v_p_3742_, lean_box(0));
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3787_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3748_ = v___x_3745_;
v_isShared_3749_ = v_isSharedCheck_3787_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3787_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
uint8_t v___x_3750_; 
v___x_3750_ = lean_unbox(v_a_3746_);
lean_dec(v_a_3746_);
if (v___x_3750_ == 0)
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3754_; 
lean_dec_ref(v_p_3742_);
lean_dec_ref(v_enter_3741_);
v___x_3751_ = lean_box(0);
v___x_3752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3751_);
lean_ctor_set(v___x_3752_, 1, v_a_3743_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3752_);
v___x_3754_ = v___x_3748_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3752_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
else
{
lean_object* v___x_3756_; 
lean_del_object(v___x_3748_);
v___x_3756_ = lean_io_read_dir(v_p_3742_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3758_; size_t v_sz_3759_; size_t v___x_3760_; lean_object* v___x_3761_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
lean_dec_ref(v___x_3756_);
v___x_3758_ = lean_box(0);
v_sz_3759_ = lean_array_size(v_a_3757_);
v___x_3760_ = ((size_t)0ULL);
v___x_3761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_3741_, v_p_3742_, v_a_3757_, v_sz_3759_, v___x_3760_, v___x_3758_, v_a_3743_);
lean_dec(v_a_3757_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3778_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3764_ = v___x_3761_;
v_isShared_3765_ = v_isSharedCheck_3778_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3761_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3778_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v_snd_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3776_; 
v_snd_3766_ = lean_ctor_get(v_a_3762_, 1);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_a_3762_);
if (v_isSharedCheck_3776_ == 0)
{
lean_object* v_unused_3777_; 
v_unused_3777_ = lean_ctor_get(v_a_3762_, 0);
lean_dec(v_unused_3777_);
v___x_3768_ = v_a_3762_;
v_isShared_3769_ = v_isSharedCheck_3776_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_snd_3766_);
lean_dec(v_a_3762_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3776_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 0, v___x_3758_);
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3758_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_snd_3766_);
v___x_3771_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3773_; 
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 0, v___x_3771_);
v___x_3773_ = v___x_3764_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
}
else
{
return v___x_3761_;
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec_ref(v_a_3743_);
lean_dec_ref(v_p_3742_);
lean_dec_ref(v_enter_3741_);
v_a_3779_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3756_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3756_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref(v_a_3743_);
lean_dec_ref(v_p_3742_);
lean_dec_ref(v_enter_3741_);
v_a_3788_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3745_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3745_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go___boxed(lean_object* v_enter_3796_, lean_object* v_p_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3796_, v_p_3797_, v_a_3798_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0___boxed(lean_object* v_enter_3801_, lean_object* v_p_3802_, lean_object* v_as_3803_, lean_object* v_sz_3804_, lean_object* v_i_3805_, lean_object* v_b_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
size_t v_sz_boxed_3809_; size_t v_i_boxed_3810_; lean_object* v_res_3811_; 
v_sz_boxed_3809_ = lean_unbox_usize(v_sz_3804_);
lean_dec(v_sz_3804_);
v_i_boxed_3810_ = lean_unbox_usize(v_i_3805_);
lean_dec(v_i_3805_);
v_res_3811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_3801_, v_p_3802_, v_as_3803_, v_sz_boxed_3809_, v_i_boxed_3810_, v_b_3806_, v___y_3807_);
lean_dec_ref(v_as_3803_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object* v_p_3812_, lean_object* v_enter_3813_){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3815_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_3816_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3813_, v_p_3812_, v___x_3815_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3825_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3819_ = v___x_3816_;
v_isShared_3820_ = v_isSharedCheck_3825_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3816_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3825_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v_snd_3821_; lean_object* v___x_3823_; 
v_snd_3821_ = lean_ctor_get(v_a_3817_, 1);
lean_inc(v_snd_3821_);
lean_dec(v_a_3817_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v_snd_3821_);
v___x_3823_ = v___x_3819_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_snd_3821_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
v_a_3826_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3816_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3816_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir___boxed(lean_object* v_p_3834_, lean_object* v_enter_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_System_FilePath_walkDir(v_p_3834_, v_enter_3835_);
return v_res_3837_;
}
}
static lean_object* _init_l_IO_FS_readBinFile___closed__0(void){
_start:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3838_ = lean_unsigned_to_nat(0u);
v___x_3839_ = lean_mk_empty_byte_array(v___x_3838_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object* v_fname_3840_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = lean_io_metadata(v_fname_3840_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; uint8_t v___x_3844_; lean_object* v___x_3845_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3843_);
lean_dec_ref(v___x_3842_);
v___x_3844_ = 0;
v___x_3845_ = lean_io_prim_handle_mk(v_fname_3840_, v___x_3844_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; uint64_t v_byteSize_3847_; size_t v___x_3848_; size_t v___x_3849_; uint8_t v___x_3850_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref(v___x_3845_);
v_byteSize_3847_ = lean_ctor_get_uint64(v_a_3843_, sizeof(void*)*2);
lean_dec(v_a_3843_);
v___x_3848_ = lean_uint64_to_usize(v_byteSize_3847_);
v___x_3849_ = ((size_t)0ULL);
v___x_3850_ = lean_usize_dec_lt(v___x_3849_, v___x_3848_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = lean_obj_once(&l_IO_FS_readBinFile___closed__0, &l_IO_FS_readBinFile___closed__0_once, _init_l_IO_FS_readBinFile___closed__0);
v___x_3852_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_a_3846_, v___x_3851_);
lean_dec(v_a_3846_);
return v___x_3852_;
}
else
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_io_prim_handle_read(v_a_3846_, v___x_3848_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3855_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref(v___x_3853_);
v___x_3855_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_a_3846_, v_a_3854_);
lean_dec(v_a_3846_);
return v___x_3855_;
}
else
{
lean_dec(v_a_3846_);
return v___x_3853_;
}
}
}
else
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
lean_dec(v_a_3843_);
v_a_3856_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3845_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3845_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
v_a_3864_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3842_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3842_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object* v_fname_3872_, lean_object* v_a_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_IO_FS_readBinFile(v_fname_3872_);
lean_dec_ref(v_fname_3872_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object* v_fname_3877_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l_IO_FS_readBinFile(v_fname_3877_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3897_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3882_ = v___x_3879_;
v_isShared_3883_ = v_isSharedCheck_3897_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3879_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3897_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
uint8_t v___x_3884_; 
v___x_3884_ = lean_string_validate_utf8(v_a_3880_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3891_; 
lean_dec(v_a_3880_);
v___x_3885_ = ((lean_object*)(l_IO_FS_readFile___closed__0));
v___x_3886_ = lean_string_append(v___x_3885_, v_fname_3877_);
v___x_3887_ = ((lean_object*)(l_IO_FS_readFile___closed__1));
v___x_3888_ = lean_string_append(v___x_3886_, v___x_3887_);
v___x_3889_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set_tag(v___x_3882_, 1);
lean_ctor_set(v___x_3882_, 0, v___x_3889_);
v___x_3891_ = v___x_3882_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3889_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
else
{
lean_object* v___x_3893_; lean_object* v___x_3895_; 
v___x_3893_ = lean_string_from_utf8_unchecked(v_a_3880_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 0, v___x_3893_);
v___x_3895_ = v___x_3882_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
v_a_3898_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3879_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3879_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object* v_fname_3906_, lean_object* v_a_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_IO_FS_readFile(v_fname_3906_);
lean_dec_ref(v_fname_3906_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0(lean_object* v_x_3909_){
_start:
{
lean_object* v_fst_3910_; 
v_fst_3910_ = lean_ctor_get(v_x_3909_, 0);
lean_inc(v_fst_3910_);
return v_fst_3910_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0___boxed(lean_object* v_x_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_IO_withStdin___redArg___lam__0(v_x_3911_);
lean_dec_ref(v_x_3911_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1(lean_object* v___x_3913_, lean_object* v_x_3914_){
_start:
{
lean_inc(v___x_3913_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1___boxed(lean_object* v___x_3915_, lean_object* v_x_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l_IO_withStdin___redArg___lam__1(v___x_3915_, v_x_3916_);
lean_dec(v_x_3916_);
lean_dec(v___x_3915_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__2(lean_object* v_toFunctor_3918_, lean_object* v_inst_3919_, lean_object* v_inst_3920_, lean_object* v_x_3921_, lean_object* v___f_3922_, lean_object* v_prev_3923_){
_start:
{
lean_object* v_map_3924_; lean_object* v_mapConst_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___f_3930_; lean_object* v_y_3931_; lean_object* v___x_3932_; 
v_map_3924_ = lean_ctor_get(v_toFunctor_3918_, 0);
lean_inc(v_map_3924_);
v_mapConst_3925_ = lean_ctor_get(v_toFunctor_3918_, 1);
lean_inc(v_mapConst_3925_);
lean_dec_ref(v_toFunctor_3918_);
v___x_3926_ = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(v___x_3926_, 0, v_prev_3923_);
v___x_3927_ = lean_apply_2(v_inst_3919_, lean_box(0), v___x_3926_);
v___x_3928_ = lean_box(0);
v___x_3929_ = lean_apply_4(v_mapConst_3925_, lean_box(0), lean_box(0), v___x_3928_, v___x_3927_);
v___f_3930_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3930_, 0, v___x_3929_);
v_y_3931_ = lean_apply_4(v_inst_3920_, lean_box(0), lean_box(0), v_x_3921_, v___f_3930_);
v___x_3932_ = lean_apply_4(v_map_3924_, lean_box(0), lean_box(0), v___f_3922_, v_y_3931_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg(lean_object* v_inst_3934_, lean_object* v_inst_3935_, lean_object* v_inst_3936_, lean_object* v_h_3937_, lean_object* v_x_3938_){
_start:
{
lean_object* v_toApplicative_3939_; lean_object* v_toBind_3940_; lean_object* v_toFunctor_3941_; lean_object* v___f_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___f_3945_; lean_object* v___x_3946_; 
v_toApplicative_3939_ = lean_ctor_get(v_inst_3934_, 0);
lean_inc_ref(v_toApplicative_3939_);
v_toBind_3940_ = lean_ctor_get(v_inst_3934_, 1);
lean_inc(v_toBind_3940_);
lean_dec_ref(v_inst_3934_);
v_toFunctor_3941_ = lean_ctor_get(v_toApplicative_3939_, 0);
lean_inc_ref(v_toFunctor_3941_);
lean_dec_ref(v_toApplicative_3939_);
v___f_3942_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3943_ = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(v___x_3943_, 0, v_h_3937_);
lean_inc(v_inst_3936_);
v___x_3944_ = lean_apply_2(v_inst_3936_, lean_box(0), v___x_3943_);
v___f_3945_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3945_, 0, v_toFunctor_3941_);
lean_closure_set(v___f_3945_, 1, v_inst_3936_);
lean_closure_set(v___f_3945_, 2, v_inst_3935_);
lean_closure_set(v___f_3945_, 3, v_x_3938_);
lean_closure_set(v___f_3945_, 4, v___f_3942_);
v___x_3946_ = lean_apply_4(v_toBind_3940_, lean_box(0), lean_box(0), v___x_3944_, v___f_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object* v_m_3947_, lean_object* v_00_u03b1_3948_, lean_object* v_inst_3949_, lean_object* v_inst_3950_, lean_object* v_inst_3951_, lean_object* v_h_3952_, lean_object* v_x_3953_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l_IO_withStdin___redArg(v_inst_3949_, v_inst_3950_, v_inst_3951_, v_h_3952_, v_x_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg___lam__2(lean_object* v_toFunctor_3955_, lean_object* v_inst_3956_, lean_object* v_inst_3957_, lean_object* v_x_3958_, lean_object* v___f_3959_, lean_object* v_prev_3960_){
_start:
{
lean_object* v_map_3961_; lean_object* v_mapConst_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___f_3967_; lean_object* v_y_3968_; lean_object* v___x_3969_; 
v_map_3961_ = lean_ctor_get(v_toFunctor_3955_, 0);
lean_inc(v_map_3961_);
v_mapConst_3962_ = lean_ctor_get(v_toFunctor_3955_, 1);
lean_inc(v_mapConst_3962_);
lean_dec_ref(v_toFunctor_3955_);
v___x_3963_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_3963_, 0, v_prev_3960_);
v___x_3964_ = lean_apply_2(v_inst_3956_, lean_box(0), v___x_3963_);
v___x_3965_ = lean_box(0);
v___x_3966_ = lean_apply_4(v_mapConst_3962_, lean_box(0), lean_box(0), v___x_3965_, v___x_3964_);
v___f_3967_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3967_, 0, v___x_3966_);
v_y_3968_ = lean_apply_4(v_inst_3957_, lean_box(0), lean_box(0), v_x_3958_, v___f_3967_);
v___x_3969_ = lean_apply_4(v_map_3961_, lean_box(0), lean_box(0), v___f_3959_, v_y_3968_);
return v___x_3969_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg(lean_object* v_inst_3970_, lean_object* v_inst_3971_, lean_object* v_inst_3972_, lean_object* v_h_3973_, lean_object* v_x_3974_){
_start:
{
lean_object* v_toApplicative_3975_; lean_object* v_toBind_3976_; lean_object* v_toFunctor_3977_; lean_object* v___f_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___f_3981_; lean_object* v___x_3982_; 
v_toApplicative_3975_ = lean_ctor_get(v_inst_3970_, 0);
lean_inc_ref(v_toApplicative_3975_);
v_toBind_3976_ = lean_ctor_get(v_inst_3970_, 1);
lean_inc(v_toBind_3976_);
lean_dec_ref(v_inst_3970_);
v_toFunctor_3977_ = lean_ctor_get(v_toApplicative_3975_, 0);
lean_inc_ref(v_toFunctor_3977_);
lean_dec_ref(v_toApplicative_3975_);
v___f_3978_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3979_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_3979_, 0, v_h_3973_);
lean_inc(v_inst_3972_);
v___x_3980_ = lean_apply_2(v_inst_3972_, lean_box(0), v___x_3979_);
v___f_3981_ = lean_alloc_closure((void*)(l_IO_withStdout___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3981_, 0, v_toFunctor_3977_);
lean_closure_set(v___f_3981_, 1, v_inst_3972_);
lean_closure_set(v___f_3981_, 2, v_inst_3971_);
lean_closure_set(v___f_3981_, 3, v_x_3974_);
lean_closure_set(v___f_3981_, 4, v___f_3978_);
v___x_3982_ = lean_apply_4(v_toBind_3976_, lean_box(0), lean_box(0), v___x_3980_, v___f_3981_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object* v_m_3983_, lean_object* v_00_u03b1_3984_, lean_object* v_inst_3985_, lean_object* v_inst_3986_, lean_object* v_inst_3987_, lean_object* v_h_3988_, lean_object* v_x_3989_){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_IO_withStdout___redArg(v_inst_3985_, v_inst_3986_, v_inst_3987_, v_h_3988_, v_x_3989_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg___lam__2(lean_object* v_toFunctor_3991_, lean_object* v_inst_3992_, lean_object* v_inst_3993_, lean_object* v_x_3994_, lean_object* v___f_3995_, lean_object* v_prev_3996_){
_start:
{
lean_object* v_map_3997_; lean_object* v_mapConst_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___f_4003_; lean_object* v_y_4004_; lean_object* v___x_4005_; 
v_map_3997_ = lean_ctor_get(v_toFunctor_3991_, 0);
lean_inc(v_map_3997_);
v_mapConst_3998_ = lean_ctor_get(v_toFunctor_3991_, 1);
lean_inc(v_mapConst_3998_);
lean_dec_ref(v_toFunctor_3991_);
v___x_3999_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_3999_, 0, v_prev_3996_);
v___x_4000_ = lean_apply_2(v_inst_3992_, lean_box(0), v___x_3999_);
v___x_4001_ = lean_box(0);
v___x_4002_ = lean_apply_4(v_mapConst_3998_, lean_box(0), lean_box(0), v___x_4001_, v___x_4000_);
v___f_4003_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4003_, 0, v___x_4002_);
v_y_4004_ = lean_apply_4(v_inst_3993_, lean_box(0), lean_box(0), v_x_3994_, v___f_4003_);
v___x_4005_ = lean_apply_4(v_map_3997_, lean_box(0), lean_box(0), v___f_3995_, v_y_4004_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg(lean_object* v_inst_4006_, lean_object* v_inst_4007_, lean_object* v_inst_4008_, lean_object* v_h_4009_, lean_object* v_x_4010_){
_start:
{
lean_object* v_toApplicative_4011_; lean_object* v_toBind_4012_; lean_object* v_toFunctor_4013_; lean_object* v___f_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___f_4017_; lean_object* v___x_4018_; 
v_toApplicative_4011_ = lean_ctor_get(v_inst_4006_, 0);
lean_inc_ref(v_toApplicative_4011_);
v_toBind_4012_ = lean_ctor_get(v_inst_4006_, 1);
lean_inc(v_toBind_4012_);
lean_dec_ref(v_inst_4006_);
v_toFunctor_4013_ = lean_ctor_get(v_toApplicative_4011_, 0);
lean_inc_ref(v_toFunctor_4013_);
lean_dec_ref(v_toApplicative_4011_);
v___f_4014_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4015_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_4015_, 0, v_h_4009_);
lean_inc(v_inst_4008_);
v___x_4016_ = lean_apply_2(v_inst_4008_, lean_box(0), v___x_4015_);
v___f_4017_ = lean_alloc_closure((void*)(l_IO_withStderr___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4017_, 0, v_toFunctor_4013_);
lean_closure_set(v___f_4017_, 1, v_inst_4008_);
lean_closure_set(v___f_4017_, 2, v_inst_4007_);
lean_closure_set(v___f_4017_, 3, v_x_4010_);
lean_closure_set(v___f_4017_, 4, v___f_4014_);
v___x_4018_ = lean_apply_4(v_toBind_4012_, lean_box(0), lean_box(0), v___x_4016_, v___f_4017_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object* v_m_4019_, lean_object* v_00_u03b1_4020_, lean_object* v_inst_4021_, lean_object* v_inst_4022_, lean_object* v_inst_4023_, lean_object* v_h_4024_, lean_object* v_x_4025_){
_start:
{
lean_object* v___x_4026_; 
v___x_4026_ = l_IO_withStderr___redArg(v_inst_4021_, v_inst_4022_, v_inst_4023_, v_h_4024_, v_x_4025_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_IO_print___redArg(lean_object* v_inst_4027_, lean_object* v_s_4028_){
_start:
{
lean_object* v___x_4030_; lean_object* v_putStr_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4030_ = lean_get_stdout();
v_putStr_4031_ = lean_ctor_get(v___x_4030_, 4);
lean_inc_ref(v_putStr_4031_);
lean_dec_ref(v___x_4030_);
v___x_4032_ = lean_apply_1(v_inst_4027_, v_s_4028_);
v___x_4033_ = lean_apply_2(v_putStr_4031_, v___x_4032_, lean_box(0));
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_IO_print___redArg___boxed(lean_object* v_inst_4034_, lean_object* v_s_4035_, lean_object* v_a_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_IO_print___redArg(v_inst_4034_, v_s_4035_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_IO_print(lean_object* v_00_u03b1_4038_, lean_object* v_inst_4039_, lean_object* v_s_4040_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_IO_print___redArg(v_inst_4039_, v_s_4040_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_IO_print___boxed(lean_object* v_00_u03b1_4043_, lean_object* v_inst_4044_, lean_object* v_s_4045_, lean_object* v_a_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_IO_print(v_00_u03b1_4043_, v_inst_4044_, v_s_4045_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_IO_println___redArg(lean_object* v_inst_4049_, lean_object* v_s_4050_){
_start:
{
lean_object* v___f_4052_; lean_object* v___x_4053_; uint32_t v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___f_4052_ = ((lean_object*)(l_IO_println___redArg___closed__0));
v___x_4053_ = lean_apply_1(v_inst_4049_, v_s_4050_);
v___x_4054_ = 10;
v___x_4055_ = lean_string_push(v___x_4053_, v___x_4054_);
v___x_4056_ = l_IO_print___redArg(v___f_4052_, v___x_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_IO_println___redArg___boxed(lean_object* v_inst_4057_, lean_object* v_s_4058_, lean_object* v_a_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l_IO_println___redArg(v_inst_4057_, v_s_4058_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l_IO_println(lean_object* v_00_u03b1_4061_, lean_object* v_inst_4062_, lean_object* v_s_4063_){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = l_IO_println___redArg(v_inst_4062_, v_s_4063_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_IO_println___boxed(lean_object* v_00_u03b1_4066_, lean_object* v_inst_4067_, lean_object* v_s_4068_, lean_object* v_a_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_IO_println(v_00_u03b1_4066_, v_inst_4067_, v_s_4068_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg(lean_object* v_inst_4071_, lean_object* v_s_4072_){
_start:
{
lean_object* v___x_4074_; lean_object* v_putStr_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4074_ = lean_get_stderr();
v_putStr_4075_ = lean_ctor_get(v___x_4074_, 4);
lean_inc_ref(v_putStr_4075_);
lean_dec_ref(v___x_4074_);
v___x_4076_ = lean_apply_1(v_inst_4071_, v_s_4072_);
v___x_4077_ = lean_apply_2(v_putStr_4075_, v___x_4076_, lean_box(0));
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg___boxed(lean_object* v_inst_4078_, lean_object* v_s_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_IO_eprint___redArg(v_inst_4078_, v_s_4079_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint(lean_object* v_00_u03b1_4082_, lean_object* v_inst_4083_, lean_object* v_s_4084_){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l_IO_eprint___redArg(v_inst_4083_, v_s_4084_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___boxed(lean_object* v_00_u03b1_4087_, lean_object* v_inst_4088_, lean_object* v_s_4089_, lean_object* v_a_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_IO_eprint(v_00_u03b1_4087_, v_inst_4088_, v_s_4089_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg(lean_object* v_inst_4092_, lean_object* v_s_4093_){
_start:
{
lean_object* v___f_4095_; lean_object* v___x_4096_; uint32_t v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___f_4095_ = ((lean_object*)(l_IO_println___redArg___closed__0));
v___x_4096_ = lean_apply_1(v_inst_4092_, v_s_4093_);
v___x_4097_ = 10;
v___x_4098_ = lean_string_push(v___x_4096_, v___x_4097_);
v___x_4099_ = l_IO_eprint___redArg(v___f_4095_, v___x_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg___boxed(lean_object* v_inst_4100_, lean_object* v_s_4101_, lean_object* v_a_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_IO_eprintln___redArg(v_inst_4100_, v_s_4101_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object* v_00_u03b1_4104_, lean_object* v_inst_4105_, lean_object* v_s_4106_){
_start:
{
lean_object* v___x_4108_; 
v___x_4108_ = l_IO_eprintln___redArg(v_inst_4105_, v_s_4106_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___boxed(lean_object* v_00_u03b1_4109_, lean_object* v_inst_4110_, lean_object* v_s_4111_, lean_object* v_a_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l_IO_eprintln(v_00_u03b1_4109_, v_inst_4110_, v_s_4111_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object* v_s_4114_){
_start:
{
lean_object* v___x_4116_; lean_object* v_putStr_4117_; lean_object* v___x_4118_; 
v___x_4116_ = lean_get_stderr();
v_putStr_4117_ = lean_ctor_get(v___x_4116_, 4);
lean_inc_ref(v_putStr_4117_);
lean_dec_ref(v___x_4116_);
v___x_4118_ = lean_apply_2(v_putStr_4117_, v_s_4114_, lean_box(0));
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0___boxed(lean_object* v_s_4119_, lean_object* v_a_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_4119_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* lean_io_eprint(lean_object* v_s_4122_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_4122_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintAux___boxed(lean_object* v_s_4125_, lean_object* v_a_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = lean_io_eprint(v_s_4125_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object* v_s_4128_){
_start:
{
uint32_t v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4130_ = 10;
v___x_4131_ = lean_string_push(v_s_4128_, v___x_4130_);
v___x_4132_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v___x_4131_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0___boxed(lean_object* v_s_4133_, lean_object* v_a_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_4133_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object* v_s_4136_){
_start:
{
lean_object* v___x_4138_; 
v___x_4138_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_4136_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintlnAux___boxed(lean_object* v_s_4139_, lean_object* v_a_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = lean_io_eprintln(v_s_4139_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l_IO_appDir(){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = lean_io_app_path();
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4161_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4148_ = v___x_4145_;
v_isShared_4149_ = v_isSharedCheck_4161_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4145_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4161_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4150_; 
lean_inc(v_a_4146_);
v___x_4150_ = l_System_FilePath_parent(v_a_4146_);
if (lean_obj_tag(v___x_4150_) == 1)
{
lean_object* v_val_4151_; lean_object* v___x_4152_; 
lean_del_object(v___x_4148_);
lean_dec(v_a_4146_);
v_val_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_val_4151_);
lean_dec_ref(v___x_4150_);
v___x_4152_ = lean_io_realpath(v_val_4151_);
return v___x_4152_;
}
else
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4159_; 
lean_dec(v___x_4150_);
v___x_4153_ = ((lean_object*)(l_IO_appDir___closed__0));
v___x_4154_ = lean_string_append(v___x_4153_, v_a_4146_);
lean_dec(v_a_4146_);
v___x_4155_ = ((lean_object*)(l_IO_appDir___closed__1));
v___x_4156_ = lean_string_append(v___x_4154_, v___x_4155_);
v___x_4157_ = lean_mk_io_user_error(v___x_4156_);
if (v_isShared_4149_ == 0)
{
lean_ctor_set_tag(v___x_4148_, 1);
lean_ctor_set(v___x_4148_, 0, v___x_4157_);
v___x_4159_ = v___x_4148_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4157_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
else
{
return v___x_4145_;
}
}
}
LEAN_EXPORT lean_object* l_IO_appDir___boxed(lean_object* v_a_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_IO_appDir();
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object* v_p_4164_){
_start:
{
uint8_t v___x_4181_; 
v___x_4181_ = l_System_FilePath_isDir(v_p_4164_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4182_; 
lean_inc_ref(v_p_4164_);
v___x_4182_ = l_System_FilePath_parent(v_p_4164_);
if (lean_obj_tag(v___x_4182_) == 1)
{
lean_object* v_val_4183_; lean_object* v___x_4184_; 
v_val_4183_ = lean_ctor_get(v___x_4182_, 0);
lean_inc(v_val_4183_);
lean_dec_ref(v___x_4182_);
v___x_4184_ = l_IO_FS_createDirAll(v_val_4183_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_dec_ref(v___x_4184_);
goto v___jp_4166_;
}
else
{
lean_dec_ref(v_p_4164_);
return v___x_4184_;
}
}
else
{
lean_dec(v___x_4182_);
goto v___jp_4166_;
}
}
else
{
lean_object* v___x_4185_; lean_object* v___x_4186_; 
lean_dec_ref(v_p_4164_);
v___x_4185_ = lean_box(0);
v___x_4186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
return v___x_4186_;
}
v___jp_4166_:
{
lean_object* v___x_4167_; 
v___x_4167_ = lean_io_create_dir(v_p_4164_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_dec_ref(v_p_4164_);
return v___x_4167_;
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4180_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4170_ = v___x_4167_;
v_isShared_4171_ = v_isSharedCheck_4180_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4167_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4180_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
uint8_t v___x_4172_; 
v___x_4172_ = l_System_FilePath_isDir(v_p_4164_);
lean_dec_ref(v_p_4164_);
if (v___x_4172_ == 0)
{
lean_object* v___x_4174_; 
if (v_isShared_4171_ == 0)
{
v___x_4174_ = v___x_4170_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4168_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
else
{
lean_object* v___x_4176_; lean_object* v___x_4178_; 
lean_dec(v_a_4168_);
v___x_4176_ = lean_box(0);
if (v_isShared_4171_ == 0)
{
lean_ctor_set_tag(v___x_4170_, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4176_);
v___x_4178_ = v___x_4170_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v___x_4176_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object* v_p_4187_, lean_object* v_a_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_IO_FS_createDirAll(v_p_4187_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(lean_object* v_as_4190_, size_t v_sz_4191_, size_t v_i_4192_, lean_object* v_b_4193_){
_start:
{
lean_object* v_a_4196_; uint8_t v___x_4200_; 
v___x_4200_ = lean_usize_dec_lt(v_i_4192_, v_sz_4191_);
if (v___x_4200_ == 0)
{
lean_object* v___x_4201_; 
v___x_4201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4201_, 0, v_b_4193_);
return v___x_4201_;
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v_a_4202_ = lean_array_uget_borrowed(v_as_4190_, v_i_4192_);
lean_inc(v_a_4202_);
v___x_4203_ = l_IO_FS_DirEntry_path(v_a_4202_);
v___x_4204_ = lean_io_symlink_metadata(v___x_4203_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; uint8_t v_type_4206_; lean_object* v___x_4207_; uint8_t v___x_4208_; uint8_t v___x_4209_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4205_);
lean_dec_ref(v___x_4204_);
v_type_4206_ = lean_ctor_get_uint8(v_a_4205_, sizeof(void*)*2 + 16);
lean_dec(v_a_4205_);
v___x_4207_ = lean_box(0);
v___x_4208_ = 0;
v___x_4209_ = l_IO_FS_instBEqFileType_beq(v_type_4206_, v___x_4208_);
if (v___x_4209_ == 0)
{
lean_object* v___x_4210_; 
v___x_4210_ = lean_io_remove_file(v___x_4203_);
lean_dec_ref(v___x_4203_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_dec_ref(v___x_4210_);
v_a_4196_ = v___x_4207_;
goto v___jp_4195_;
}
else
{
return v___x_4210_;
}
}
else
{
lean_object* v___x_4211_; 
v___x_4211_ = l_IO_FS_removeDirAll(v___x_4203_);
lean_dec_ref(v___x_4203_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_dec_ref(v___x_4211_);
v_a_4196_ = v___x_4207_;
goto v___jp_4195_;
}
else
{
return v___x_4211_;
}
}
}
else
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
lean_dec_ref(v___x_4203_);
v_a_4212_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___x_4204_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4204_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4217_; 
if (v_isShared_4215_ == 0)
{
v___x_4217_ = v___x_4214_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_a_4212_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
v___jp_4195_:
{
size_t v___x_4197_; size_t v___x_4198_; 
v___x_4197_ = ((size_t)1ULL);
v___x_4198_ = lean_usize_add(v_i_4192_, v___x_4197_);
v_i_4192_ = v___x_4198_;
v_b_4193_ = v_a_4196_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object* v_p_4220_){
_start:
{
lean_object* v___x_4222_; 
v___x_4222_ = lean_io_read_dir(v_p_4220_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4224_; size_t v_sz_4225_; size_t v___x_4226_; lean_object* v___x_4227_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4223_);
lean_dec_ref(v___x_4222_);
v___x_4224_ = lean_box(0);
v_sz_4225_ = lean_array_size(v_a_4223_);
v___x_4226_ = ((size_t)0ULL);
v___x_4227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_a_4223_, v_sz_4225_, v___x_4226_, v___x_4224_);
lean_dec(v_a_4223_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v___x_4228_; 
lean_dec_ref(v___x_4227_);
v___x_4228_ = lean_io_remove_dir(v_p_4220_);
return v___x_4228_;
}
else
{
return v___x_4227_;
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
v_a_4229_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4222_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4222_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object* v_p_4237_, lean_object* v_a_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_IO_FS_removeDirAll(v_p_4237_);
lean_dec_ref(v_p_4237_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0___boxed(lean_object* v_as_4240_, lean_object* v_sz_4241_, lean_object* v_i_4242_, lean_object* v_b_4243_, lean_object* v___y_4244_){
_start:
{
size_t v_sz_boxed_4245_; size_t v_i_boxed_4246_; lean_object* v_res_4247_; 
v_sz_boxed_4245_ = lean_unbox_usize(v_sz_4241_);
lean_dec(v_sz_4241_);
v_i_boxed_4246_ = lean_unbox_usize(v_i_4242_);
lean_dec(v_i_4242_);
v_res_4247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_as_4240_, v_sz_boxed_4245_, v_i_boxed_4246_, v_b_4243_);
lean_dec_ref(v_as_4240_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg___lam__2(lean_object* v_toFunctor_4248_, lean_object* v_f_4249_, lean_object* v_inst_4250_, lean_object* v_inst_4251_, lean_object* v___f_4252_, lean_object* v_____x_4253_){
_start:
{
lean_object* v_fst_4254_; lean_object* v_snd_4255_; lean_object* v_map_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___f_4260_; lean_object* v_y_4261_; lean_object* v___x_4262_; 
v_fst_4254_ = lean_ctor_get(v_____x_4253_, 0);
lean_inc(v_fst_4254_);
v_snd_4255_ = lean_ctor_get(v_____x_4253_, 1);
lean_inc_n(v_snd_4255_, 2);
lean_dec_ref(v_____x_4253_);
v_map_4256_ = lean_ctor_get(v_toFunctor_4248_, 0);
lean_inc(v_map_4256_);
lean_dec_ref(v_toFunctor_4248_);
v___x_4257_ = lean_apply_2(v_f_4249_, v_fst_4254_, v_snd_4255_);
v___x_4258_ = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(v___x_4258_, 0, v_snd_4255_);
v___x_4259_ = lean_apply_2(v_inst_4250_, lean_box(0), v___x_4258_);
v___f_4260_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4260_, 0, v___x_4259_);
v_y_4261_ = lean_apply_4(v_inst_4251_, lean_box(0), lean_box(0), v___x_4257_, v___f_4260_);
v___x_4262_ = lean_apply_4(v_map_4256_, lean_box(0), lean_box(0), v___f_4252_, v_y_4261_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg(lean_object* v_inst_4264_, lean_object* v_inst_4265_, lean_object* v_inst_4266_, lean_object* v_f_4267_){
_start:
{
lean_object* v_toApplicative_4268_; lean_object* v_toBind_4269_; lean_object* v_toFunctor_4270_; lean_object* v___f_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___f_4274_; lean_object* v___x_4275_; 
v_toApplicative_4268_ = lean_ctor_get(v_inst_4264_, 0);
lean_inc_ref(v_toApplicative_4268_);
v_toBind_4269_ = lean_ctor_get(v_inst_4264_, 1);
lean_inc(v_toBind_4269_);
lean_dec_ref(v_inst_4264_);
v_toFunctor_4270_ = lean_ctor_get(v_toApplicative_4268_, 0);
lean_inc_ref(v_toFunctor_4270_);
lean_dec_ref(v_toApplicative_4268_);
v___f_4271_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4272_ = ((lean_object*)(l_IO_FS_withTempFile___redArg___closed__0));
lean_inc(v_inst_4266_);
v___x_4273_ = lean_apply_2(v_inst_4266_, lean_box(0), v___x_4272_);
v___f_4274_ = lean_alloc_closure((void*)(l_IO_FS_withTempFile___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4274_, 0, v_toFunctor_4270_);
lean_closure_set(v___f_4274_, 1, v_f_4267_);
lean_closure_set(v___f_4274_, 2, v_inst_4266_);
lean_closure_set(v___f_4274_, 3, v_inst_4265_);
lean_closure_set(v___f_4274_, 4, v___f_4271_);
v___x_4275_ = lean_apply_4(v_toBind_4269_, lean_box(0), lean_box(0), v___x_4273_, v___f_4274_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile(lean_object* v_m_4276_, lean_object* v_00_u03b1_4277_, lean_object* v_inst_4278_, lean_object* v_inst_4279_, lean_object* v_inst_4280_, lean_object* v_f_4281_){
_start:
{
lean_object* v___x_4282_; 
v___x_4282_ = l_IO_FS_withTempFile___redArg(v_inst_4278_, v_inst_4279_, v_inst_4280_, v_f_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg___lam__2(lean_object* v_toFunctor_4283_, lean_object* v_f_4284_, lean_object* v_inst_4285_, lean_object* v_inst_4286_, lean_object* v___f_4287_, lean_object* v_path_4288_){
_start:
{
lean_object* v_map_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___f_4293_; lean_object* v_y_4294_; lean_object* v___x_4295_; 
v_map_4289_ = lean_ctor_get(v_toFunctor_4283_, 0);
lean_inc(v_map_4289_);
lean_dec_ref(v_toFunctor_4283_);
lean_inc_ref(v_path_4288_);
v___x_4290_ = lean_apply_1(v_f_4284_, v_path_4288_);
v___x_4291_ = lean_alloc_closure((void*)(l_IO_FS_removeDirAll___boxed), 2, 1);
lean_closure_set(v___x_4291_, 0, v_path_4288_);
v___x_4292_ = lean_apply_2(v_inst_4285_, lean_box(0), v___x_4291_);
v___f_4293_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4293_, 0, v___x_4292_);
v_y_4294_ = lean_apply_4(v_inst_4286_, lean_box(0), lean_box(0), v___x_4290_, v___f_4293_);
v___x_4295_ = lean_apply_4(v_map_4289_, lean_box(0), lean_box(0), v___f_4287_, v_y_4294_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg(lean_object* v_inst_4297_, lean_object* v_inst_4298_, lean_object* v_inst_4299_, lean_object* v_f_4300_){
_start:
{
lean_object* v_toApplicative_4301_; lean_object* v_toBind_4302_; lean_object* v_toFunctor_4303_; lean_object* v___f_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___f_4307_; lean_object* v___x_4308_; 
v_toApplicative_4301_ = lean_ctor_get(v_inst_4297_, 0);
lean_inc_ref(v_toApplicative_4301_);
v_toBind_4302_ = lean_ctor_get(v_inst_4297_, 1);
lean_inc(v_toBind_4302_);
lean_dec_ref(v_inst_4297_);
v_toFunctor_4303_ = lean_ctor_get(v_toApplicative_4301_, 0);
lean_inc_ref(v_toFunctor_4303_);
lean_dec_ref(v_toApplicative_4301_);
v___f_4304_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4305_ = ((lean_object*)(l_IO_FS_withTempDir___redArg___closed__0));
lean_inc(v_inst_4299_);
v___x_4306_ = lean_apply_2(v_inst_4299_, lean_box(0), v___x_4305_);
v___f_4307_ = lean_alloc_closure((void*)(l_IO_FS_withTempDir___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4307_, 0, v_toFunctor_4303_);
lean_closure_set(v___f_4307_, 1, v_f_4300_);
lean_closure_set(v___f_4307_, 2, v_inst_4299_);
lean_closure_set(v___f_4307_, 3, v_inst_4298_);
lean_closure_set(v___f_4307_, 4, v___f_4304_);
v___x_4308_ = lean_apply_4(v_toBind_4302_, lean_box(0), lean_box(0), v___x_4306_, v___f_4307_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir(lean_object* v_m_4309_, lean_object* v_00_u03b1_4310_, lean_object* v_inst_4311_, lean_object* v_inst_4312_, lean_object* v_inst_4313_, lean_object* v_f_4314_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = l_IO_FS_withTempDir___redArg(v_inst_4311_, v_inst_4312_, v_inst_4313_, v_f_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_getCurrentDir___boxed(lean_object* v_a_00___x40___internal___hyg_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = lean_io_process_get_current_dir();
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_setCurrentDir___boxed(lean_object* v_path_4321_, lean_object* v_a_00___x40___internal___hyg_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = lean_io_process_set_current_dir(v_path_4321_);
lean_dec_ref(v_path_4321_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_getPID___boxed(lean_object* v_a_00___x40___internal___hyg_4325_){
_start:
{
uint32_t v_res_4326_; lean_object* v_r_4327_; 
v_res_4326_ = lean_io_process_get_pid();
v_r_4327_ = lean_box_uint32(v_res_4326_);
return v_r_4327_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx(uint8_t v_x_4328_){
_start:
{
switch(v_x_4328_)
{
case 0:
{
lean_object* v___x_4329_; 
v___x_4329_ = lean_unsigned_to_nat(0u);
return v___x_4329_;
}
case 1:
{
lean_object* v___x_4330_; 
v___x_4330_ = lean_unsigned_to_nat(1u);
return v___x_4330_;
}
default: 
{
lean_object* v___x_4331_; 
v___x_4331_ = lean_unsigned_to_nat(2u);
return v___x_4331_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx___boxed(lean_object* v_x_4332_){
_start:
{
uint8_t v_x_boxed_4333_; lean_object* v_res_4334_; 
v_x_boxed_4333_ = lean_unbox(v_x_4332_);
v_res_4334_ = l_IO_Process_Stdio_ctorIdx(v_x_boxed_4333_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx(uint8_t v_x_4335_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l_IO_Process_Stdio_ctorIdx(v_x_4335_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx___boxed(lean_object* v_x_4337_){
_start:
{
uint8_t v_x_4__boxed_4338_; lean_object* v_res_4339_; 
v_x_4__boxed_4338_ = lean_unbox(v_x_4337_);
v_res_4339_ = l_IO_Process_Stdio_toCtorIdx(v_x_4__boxed_4338_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg(lean_object* v_k_4340_){
_start:
{
lean_inc(v_k_4340_);
return v_k_4340_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg___boxed(lean_object* v_k_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_IO_Process_Stdio_ctorElim___redArg(v_k_4341_);
lean_dec(v_k_4341_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim(lean_object* v_motive_4343_, lean_object* v_ctorIdx_4344_, uint8_t v_t_4345_, lean_object* v_h_4346_, lean_object* v_k_4347_){
_start:
{
lean_inc(v_k_4347_);
return v_k_4347_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___boxed(lean_object* v_motive_4348_, lean_object* v_ctorIdx_4349_, lean_object* v_t_4350_, lean_object* v_h_4351_, lean_object* v_k_4352_){
_start:
{
uint8_t v_t_boxed_4353_; lean_object* v_res_4354_; 
v_t_boxed_4353_ = lean_unbox(v_t_4350_);
v_res_4354_ = l_IO_Process_Stdio_ctorElim(v_motive_4348_, v_ctorIdx_4349_, v_t_boxed_4353_, v_h_4351_, v_k_4352_);
lean_dec(v_k_4352_);
lean_dec(v_ctorIdx_4349_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg(lean_object* v_piped_4355_){
_start:
{
lean_inc(v_piped_4355_);
return v_piped_4355_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg___boxed(lean_object* v_piped_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l_IO_Process_Stdio_piped_elim___redArg(v_piped_4356_);
lean_dec(v_piped_4356_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim(lean_object* v_motive_4358_, uint8_t v_t_4359_, lean_object* v_h_4360_, lean_object* v_piped_4361_){
_start:
{
lean_inc(v_piped_4361_);
return v_piped_4361_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___boxed(lean_object* v_motive_4362_, lean_object* v_t_4363_, lean_object* v_h_4364_, lean_object* v_piped_4365_){
_start:
{
uint8_t v_t_boxed_4366_; lean_object* v_res_4367_; 
v_t_boxed_4366_ = lean_unbox(v_t_4363_);
v_res_4367_ = l_IO_Process_Stdio_piped_elim(v_motive_4362_, v_t_boxed_4366_, v_h_4364_, v_piped_4365_);
lean_dec(v_piped_4365_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg(lean_object* v_inherit_4368_){
_start:
{
lean_inc(v_inherit_4368_);
return v_inherit_4368_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg___boxed(lean_object* v_inherit_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_IO_Process_Stdio_inherit_elim___redArg(v_inherit_4369_);
lean_dec(v_inherit_4369_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim(lean_object* v_motive_4371_, uint8_t v_t_4372_, lean_object* v_h_4373_, lean_object* v_inherit_4374_){
_start:
{
lean_inc(v_inherit_4374_);
return v_inherit_4374_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___boxed(lean_object* v_motive_4375_, lean_object* v_t_4376_, lean_object* v_h_4377_, lean_object* v_inherit_4378_){
_start:
{
uint8_t v_t_boxed_4379_; lean_object* v_res_4380_; 
v_t_boxed_4379_ = lean_unbox(v_t_4376_);
v_res_4380_ = l_IO_Process_Stdio_inherit_elim(v_motive_4375_, v_t_boxed_4379_, v_h_4377_, v_inherit_4378_);
lean_dec(v_inherit_4378_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg(lean_object* v_null_4381_){
_start:
{
lean_inc(v_null_4381_);
return v_null_4381_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg___boxed(lean_object* v_null_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_IO_Process_Stdio_null_elim___redArg(v_null_4382_);
lean_dec(v_null_4382_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim(lean_object* v_motive_4384_, uint8_t v_t_4385_, lean_object* v_h_4386_, lean_object* v_null_4387_){
_start:
{
lean_inc(v_null_4387_);
return v_null_4387_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___boxed(lean_object* v_motive_4388_, lean_object* v_t_4389_, lean_object* v_h_4390_, lean_object* v_null_4391_){
_start:
{
uint8_t v_t_boxed_4392_; lean_object* v_res_4393_; 
v_t_boxed_4392_ = lean_unbox(v_t_4389_);
v_res_4393_ = l_IO_Process_Stdio_null_elim(v_motive_4388_, v_t_boxed_4392_, v_h_4390_, v_null_4391_);
lean_dec(v_null_4391_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object* v_args_4396_, lean_object* v_a_00___x40___internal___hyg_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = lean_io_process_spawn(v_args_4396_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object* v_cfg_4402_, lean_object* v_a_00___x40___internal___hyg_4403_, lean_object* v_a_00___x40___internal___hyg_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = lean_io_process_child_wait(v_cfg_4402_, v_a_00___x40___internal___hyg_4403_);
lean_dec_ref(v_a_00___x40___internal___hyg_4403_);
lean_dec_ref(v_cfg_4402_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_tryWait___boxed(lean_object* v_cfg_4409_, lean_object* v_a_00___x40___internal___hyg_4410_, lean_object* v_a_00___x40___internal___hyg_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = lean_io_process_child_try_wait(v_cfg_4409_, v_a_00___x40___internal___hyg_4410_);
lean_dec_ref(v_a_00___x40___internal___hyg_4410_);
lean_dec_ref(v_cfg_4409_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_kill___boxed(lean_object* v_cfg_4416_, lean_object* v_a_00___x40___internal___hyg_4417_, lean_object* v_a_00___x40___internal___hyg_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = lean_io_process_child_kill(v_cfg_4416_, v_a_00___x40___internal___hyg_4417_);
lean_dec_ref(v_a_00___x40___internal___hyg_4417_);
lean_dec_ref(v_cfg_4416_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object* v_cfg_4423_, lean_object* v_a_00___x40___internal___hyg_4424_, lean_object* v_a_00___x40___internal___hyg_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = lean_io_process_child_take_stdin(v_cfg_4423_, v_a_00___x40___internal___hyg_4424_);
lean_dec_ref(v_cfg_4423_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_pid___boxed(lean_object* v_cfg_4429_, lean_object* v_a_00___x40___internal___hyg_4430_){
_start:
{
uint32_t v_res_4431_; lean_object* v_r_4432_; 
v_res_4431_ = lean_io_process_child_pid(v_cfg_4429_, v_a_00___x40___internal___hyg_4430_);
lean_dec_ref(v_cfg_4429_);
v_r_4432_ = lean_box_uint32(v_res_4431_);
return v_r_4432_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(lean_object* v_e_4433_){
_start:
{
if (lean_obj_tag(v_e_4433_) == 0)
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4444_; 
v_a_4435_ = lean_ctor_get(v_e_4433_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v_e_4433_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4437_ = v_e_4433_;
v_isShared_4438_ = v_isSharedCheck_4444_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v_e_4433_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4444_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4442_; 
v___x_4439_ = lean_io_error_to_string(v_a_4435_);
v___x_4440_ = lean_mk_io_user_error(v___x_4439_);
if (v_isShared_4438_ == 0)
{
lean_ctor_set_tag(v___x_4437_, 1);
lean_ctor_set(v___x_4437_, 0, v___x_4440_);
v___x_4442_ = v___x_4437_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
v_a_4445_ = lean_ctor_get(v_e_4433_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v_e_4433_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v_e_4433_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v_e_4433_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
lean_ctor_set_tag(v___x_4447_, 0);
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg___boxed(lean_object* v_e_4453_, lean_object* v_a_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_4453_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0(lean_object* v_00_u03b1_4456_, lean_object* v_e_4457_){
_start:
{
lean_object* v___x_4459_; 
v___x_4459_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_4457_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___boxed(lean_object* v_00_u03b1_4460_, lean_object* v_e_4461_, lean_object* v_a_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_IO_ofExcept___at___00IO_Process_output_spec__0(v_00_u03b1_4460_, v_e_4461_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0(lean_object* v_stdout_4464_){
_start:
{
lean_object* v___x_4466_; 
v___x_4466_ = l_IO_FS_Handle_readToEnd(v_stdout_4464_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4474_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4469_ = v___x_4466_;
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4466_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4472_; 
if (v_isShared_4470_ == 0)
{
lean_ctor_set_tag(v___x_4469_, 1);
v___x_4472_ = v___x_4469_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
else
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
v_a_4475_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4466_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4466_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
lean_ctor_set_tag(v___x_4477_, 0);
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0___boxed(lean_object* v_stdout_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_IO_Process_output___lam__0(v_stdout_4483_);
lean_dec(v_stdout_4483_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object* v_args_4491_, lean_object* v_input_x3f_4492_){
_start:
{
lean_object* v_child_4495_; 
if (lean_obj_tag(v_input_x3f_4492_) == 1)
{
lean_object* v_val_4542_; lean_object* v___x_4543_; lean_object* v_cmd_4544_; lean_object* v_args_4545_; lean_object* v_cwd_4546_; lean_object* v_env_4547_; uint8_t v_inheritEnv_4548_; uint8_t v_setsid_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4596_; 
v_val_4542_ = lean_ctor_get(v_input_x3f_4492_, 0);
v___x_4543_ = ((lean_object*)(l_IO_Process_output___closed__1));
v_cmd_4544_ = lean_ctor_get(v_args_4491_, 1);
v_args_4545_ = lean_ctor_get(v_args_4491_, 2);
v_cwd_4546_ = lean_ctor_get(v_args_4491_, 3);
v_env_4547_ = lean_ctor_get(v_args_4491_, 4);
v_inheritEnv_4548_ = lean_ctor_get_uint8(v_args_4491_, sizeof(void*)*5);
v_setsid_4549_ = lean_ctor_get_uint8(v_args_4491_, sizeof(void*)*5 + 1);
v_isSharedCheck_4596_ = !lean_is_exclusive(v_args_4491_);
if (v_isSharedCheck_4596_ == 0)
{
lean_object* v_unused_4597_; 
v_unused_4597_ = lean_ctor_get(v_args_4491_, 0);
lean_dec(v_unused_4597_);
v___x_4551_ = v_args_4491_;
v_isShared_4552_ = v_isSharedCheck_4596_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_env_4547_);
lean_inc(v_cwd_4546_);
lean_inc(v_args_4545_);
lean_inc(v_cmd_4544_);
lean_dec(v_args_4491_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4596_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v___x_4543_);
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4543_);
lean_ctor_set(v_reuseFailAlloc_4595_, 1, v_cmd_4544_);
lean_ctor_set(v_reuseFailAlloc_4595_, 2, v_args_4545_);
lean_ctor_set(v_reuseFailAlloc_4595_, 3, v_cwd_4546_);
lean_ctor_set(v_reuseFailAlloc_4595_, 4, v_env_4547_);
lean_ctor_set_uint8(v_reuseFailAlloc_4595_, sizeof(void*)*5, v_inheritEnv_4548_);
lean_ctor_set_uint8(v_reuseFailAlloc_4595_, sizeof(void*)*5 + 1, v_setsid_4549_);
v___x_4554_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
lean_object* v___x_4555_; 
v___x_4555_ = lean_io_process_spawn(v___x_4554_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4557_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc(v_a_4556_);
lean_dec_ref(v___x_4555_);
v___x_4557_ = lean_io_process_child_take_stdin(v___x_4543_, v_a_4556_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_object* v_a_4558_; lean_object* v_fst_4559_; lean_object* v_snd_4560_; lean_object* v___x_4561_; 
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
lean_inc(v_a_4558_);
lean_dec_ref(v___x_4557_);
v_fst_4559_ = lean_ctor_get(v_a_4558_, 0);
lean_inc(v_fst_4559_);
v_snd_4560_ = lean_ctor_get(v_a_4558_, 1);
lean_inc(v_snd_4560_);
lean_dec(v_a_4558_);
v___x_4561_ = lean_io_prim_handle_put_str(v_fst_4559_, v_val_4542_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v___x_4562_; 
lean_dec_ref(v___x_4561_);
v___x_4562_ = lean_io_prim_handle_flush(v_fst_4559_);
lean_dec(v_fst_4559_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_dec_ref(v___x_4562_);
v_child_4495_ = v_snd_4560_;
goto v___jp_4494_;
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec(v_snd_4560_);
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4562_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4562_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec(v_snd_4560_);
lean_dec(v_fst_4559_);
v_a_4571_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4561_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4561_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
v_a_4579_ = lean_ctor_get(v___x_4557_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4557_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4557_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
else
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
v_a_4587_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4589_ = v___x_4555_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4555_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4587_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
}
}
}
else
{
lean_object* v___x_4598_; lean_object* v_cmd_4599_; lean_object* v_args_4600_; lean_object* v_cwd_4601_; lean_object* v_env_4602_; uint8_t v_inheritEnv_4603_; uint8_t v_setsid_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4621_; 
v___x_4598_ = ((lean_object*)(l_IO_Process_output___closed__0));
v_cmd_4599_ = lean_ctor_get(v_args_4491_, 1);
v_args_4600_ = lean_ctor_get(v_args_4491_, 2);
v_cwd_4601_ = lean_ctor_get(v_args_4491_, 3);
v_env_4602_ = lean_ctor_get(v_args_4491_, 4);
v_inheritEnv_4603_ = lean_ctor_get_uint8(v_args_4491_, sizeof(void*)*5);
v_setsid_4604_ = lean_ctor_get_uint8(v_args_4491_, sizeof(void*)*5 + 1);
v_isSharedCheck_4621_ = !lean_is_exclusive(v_args_4491_);
if (v_isSharedCheck_4621_ == 0)
{
lean_object* v_unused_4622_; 
v_unused_4622_ = lean_ctor_get(v_args_4491_, 0);
lean_dec(v_unused_4622_);
v___x_4606_ = v_args_4491_;
v_isShared_4607_ = v_isSharedCheck_4621_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_env_4602_);
lean_inc(v_cwd_4601_);
lean_inc(v_args_4600_);
lean_inc(v_cmd_4599_);
lean_dec(v_args_4491_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4621_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
lean_ctor_set(v___x_4606_, 0, v___x_4598_);
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4598_);
lean_ctor_set(v_reuseFailAlloc_4620_, 1, v_cmd_4599_);
lean_ctor_set(v_reuseFailAlloc_4620_, 2, v_args_4600_);
lean_ctor_set(v_reuseFailAlloc_4620_, 3, v_cwd_4601_);
lean_ctor_set(v_reuseFailAlloc_4620_, 4, v_env_4602_);
lean_ctor_set_uint8(v_reuseFailAlloc_4620_, sizeof(void*)*5, v_inheritEnv_4603_);
lean_ctor_set_uint8(v_reuseFailAlloc_4620_, sizeof(void*)*5 + 1, v_setsid_4604_);
v___x_4609_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v___x_4610_; 
v___x_4610_ = lean_io_process_spawn(v___x_4609_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_a_4611_; 
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
lean_inc(v_a_4611_);
lean_dec_ref(v___x_4610_);
v_child_4495_ = v_a_4611_;
goto v___jp_4494_;
}
else
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4619_; 
v_a_4612_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4614_ = v___x_4610_;
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4610_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4617_; 
if (v_isShared_4615_ == 0)
{
v___x_4617_ = v___x_4614_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_a_4612_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
}
}
}
v___jp_4494_:
{
lean_object* v_stdout_4496_; lean_object* v_stderr_4497_; lean_object* v___f_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_stdout_4496_ = lean_ctor_get(v_child_4495_, 1);
v_stderr_4497_ = lean_ctor_get(v_child_4495_, 2);
lean_inc(v_stdout_4496_);
v___f_4498_ = lean_alloc_closure((void*)(l_IO_Process_output___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4498_, 0, v_stdout_4496_);
v___x_4499_ = lean_unsigned_to_nat(9u);
v___x_4500_ = lean_io_as_task(v___f_4498_, v___x_4499_);
v___x_4501_ = l_IO_FS_Handle_readToEnd(v_stderr_4497_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref(v___x_4501_);
v___x_4503_ = ((lean_object*)(l_IO_Process_output___closed__0));
v___x_4504_ = lean_io_process_child_wait(v___x_4503_, v_child_4495_);
lean_dec_ref(v_child_4495_);
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_object* v_a_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v_a_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_a_4505_);
lean_dec_ref(v___x_4504_);
v___x_4506_ = lean_task_get_own(v___x_4500_);
v___x_4507_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v___x_4506_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4517_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4510_ = v___x_4507_;
v_isShared_4511_ = v_isSharedCheck_4517_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4507_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4517_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4512_; uint32_t v___x_4513_; lean_object* v___x_4515_; 
v___x_4512_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4512_, 0, v_a_4508_);
lean_ctor_set(v___x_4512_, 1, v_a_4502_);
v___x_4513_ = lean_unbox_uint32(v_a_4505_);
lean_dec(v_a_4505_);
lean_ctor_set_uint32(v___x_4512_, sizeof(void*)*2, v___x_4513_);
if (v_isShared_4511_ == 0)
{
lean_ctor_set(v___x_4510_, 0, v___x_4512_);
v___x_4515_ = v___x_4510_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4512_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
else
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4525_; 
lean_dec(v_a_4505_);
lean_dec(v_a_4502_);
v_a_4518_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4520_ = v___x_4507_;
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4507_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4523_; 
if (v_isShared_4521_ == 0)
{
v___x_4523_ = v___x_4520_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_a_4518_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
lean_dec(v_a_4502_);
lean_dec_ref(v___x_4500_);
v_a_4526_ = lean_ctor_get(v___x_4504_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4504_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4504_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4504_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
lean_dec_ref(v___x_4500_);
lean_dec_ref(v_child_4495_);
v_a_4534_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4501_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4501_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___boxed(lean_object* v_args_4623_, lean_object* v_input_x3f_4624_, lean_object* v_a_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l_IO_Process_output(v_args_4623_, v_input_x3f_4624_);
lean_dec(v_input_x3f_4624_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_run(lean_object* v_args_4630_, lean_object* v_input_x3f_4631_){
_start:
{
lean_object* v___x_4633_; 
lean_inc_ref(v_args_4630_);
v___x_4633_ = l_IO_Process_output(v_args_4630_, v_input_x3f_4631_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4661_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4636_ = v___x_4633_;
v_isShared_4637_ = v_isSharedCheck_4661_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4633_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4661_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
uint32_t v_exitCode_4638_; lean_object* v_stdout_4639_; lean_object* v_stderr_4640_; uint32_t v___x_4641_; uint8_t v___x_4642_; 
v_exitCode_4638_ = lean_ctor_get_uint32(v_a_4634_, sizeof(void*)*2);
v_stdout_4639_ = lean_ctor_get(v_a_4634_, 0);
lean_inc_ref(v_stdout_4639_);
v_stderr_4640_ = lean_ctor_get(v_a_4634_, 1);
lean_inc_ref(v_stderr_4640_);
lean_dec(v_a_4634_);
v___x_4641_ = 0;
v___x_4642_ = lean_uint32_dec_eq(v_exitCode_4638_, v___x_4641_);
if (v___x_4642_ == 0)
{
lean_object* v_cmd_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4656_; 
lean_dec_ref(v_stdout_4639_);
v_cmd_4643_ = lean_ctor_get(v_args_4630_, 1);
lean_inc_ref(v_cmd_4643_);
lean_dec_ref(v_args_4630_);
v___x_4644_ = ((lean_object*)(l_IO_Process_run___closed__0));
v___x_4645_ = lean_string_append(v___x_4644_, v_cmd_4643_);
lean_dec_ref(v_cmd_4643_);
v___x_4646_ = ((lean_object*)(l_IO_Process_run___closed__1));
v___x_4647_ = lean_string_append(v___x_4645_, v___x_4646_);
v___x_4648_ = lean_uint32_to_nat(v_exitCode_4638_);
v___x_4649_ = l_Nat_reprFast(v___x_4648_);
v___x_4650_ = lean_string_append(v___x_4647_, v___x_4649_);
lean_dec_ref(v___x_4649_);
v___x_4651_ = ((lean_object*)(l_IO_Process_run___closed__2));
v___x_4652_ = lean_string_append(v___x_4650_, v___x_4651_);
v___x_4653_ = lean_string_append(v___x_4652_, v_stderr_4640_);
lean_dec_ref(v_stderr_4640_);
v___x_4654_ = lean_mk_io_user_error(v___x_4653_);
if (v_isShared_4637_ == 0)
{
lean_ctor_set_tag(v___x_4636_, 1);
lean_ctor_set(v___x_4636_, 0, v___x_4654_);
v___x_4656_ = v___x_4636_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v___x_4654_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
else
{
lean_object* v___x_4659_; 
lean_dec_ref(v_stderr_4640_);
lean_dec_ref(v_args_4630_);
if (v_isShared_4637_ == 0)
{
lean_ctor_set(v___x_4636_, 0, v_stdout_4639_);
v___x_4659_ = v___x_4636_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_stdout_4639_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
lean_dec_ref(v_args_4630_);
v_a_4662_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4633_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4633_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4662_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_run___boxed(lean_object* v_args_4670_, lean_object* v_input_x3f_4671_, lean_object* v_a_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l_IO_Process_run(v_args_4670_, v_input_x3f_4671_);
lean_dec(v_input_x3f_4671_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object* v_00_u03b1_4677_, lean_object* v_a_00___x40___internal___hyg_4678_, lean_object* v_a_00___x40___internal___hyg_4679_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_4680_; lean_object* v_res_4681_; 
v_a_00___x40___internal___hyg_1__boxed_4680_ = lean_unbox(v_a_00___x40___internal___hyg_4678_);
v_res_4681_ = lean_io_exit(v_a_00___x40___internal___hyg_1__boxed_4680_);
return v_res_4681_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_forceExit___boxed(lean_object* v_00_u03b1_4685_, lean_object* v_a_00___x40___internal___hyg_4686_, lean_object* v_a_00___x40___internal___hyg_4687_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_4688_; lean_object* v_res_4689_; 
v_a_00___x40___internal___hyg_1__boxed_4688_ = lean_unbox(v_a_00___x40___internal___hyg_4686_);
v_res_4689_ = lean_io_force_exit(v_a_00___x40___internal___hyg_1__boxed_4688_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l_IO_getTID___boxed(lean_object* v_a_00___x40___internal___hyg_4691_){
_start:
{
uint64_t v_res_4692_; lean_object* v_r_4693_; 
v_res_4692_ = lean_io_get_tid();
v_r_4693_ = lean_box_uint64(v_res_4692_);
return v_r_4693_;
}
}
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object* v_acc_4694_){
_start:
{
uint32_t v___y_4696_; uint32_t v___y_4697_; uint32_t v___y_4698_; uint8_t v_read_4701_; uint8_t v_write_4702_; uint8_t v_execution_4703_; uint32_t v___y_4705_; uint32_t v___y_4706_; uint32_t v___y_4710_; 
v_read_4701_ = lean_ctor_get_uint8(v_acc_4694_, 0);
v_write_4702_ = lean_ctor_get_uint8(v_acc_4694_, 1);
v_execution_4703_ = lean_ctor_get_uint8(v_acc_4694_, 2);
if (v_read_4701_ == 0)
{
uint32_t v___x_4713_; 
v___x_4713_ = 0;
v___y_4710_ = v___x_4713_;
goto v___jp_4709_;
}
else
{
uint32_t v___x_4714_; 
v___x_4714_ = 4;
v___y_4710_ = v___x_4714_;
goto v___jp_4709_;
}
v___jp_4695_:
{
uint32_t v___x_4699_; uint32_t v___x_4700_; 
v___x_4699_ = lean_uint32_lor(v___y_4696_, v___y_4698_);
v___x_4700_ = lean_uint32_lor(v___y_4697_, v___x_4699_);
return v___x_4700_;
}
v___jp_4704_:
{
if (v_execution_4703_ == 0)
{
uint32_t v___x_4707_; 
v___x_4707_ = 0;
v___y_4696_ = v___y_4706_;
v___y_4697_ = v___y_4705_;
v___y_4698_ = v___x_4707_;
goto v___jp_4695_;
}
else
{
uint32_t v___x_4708_; 
v___x_4708_ = 1;
v___y_4696_ = v___y_4706_;
v___y_4697_ = v___y_4705_;
v___y_4698_ = v___x_4708_;
goto v___jp_4695_;
}
}
v___jp_4709_:
{
if (v_write_4702_ == 0)
{
uint32_t v___x_4711_; 
v___x_4711_ = 0;
v___y_4705_ = v___y_4710_;
v___y_4706_ = v___x_4711_;
goto v___jp_4704_;
}
else
{
uint32_t v___x_4712_; 
v___x_4712_ = 2;
v___y_4705_ = v___y_4710_;
v___y_4706_ = v___x_4712_;
goto v___jp_4704_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object* v_acc_4715_){
_start:
{
uint32_t v_res_4716_; lean_object* v_r_4717_; 
v_res_4716_ = l_IO_AccessRight_flags(v_acc_4715_);
lean_dec_ref(v_acc_4715_);
v_r_4717_ = lean_box_uint32(v_res_4716_);
return v_r_4717_;
}
}
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object* v_acc_4718_){
_start:
{
lean_object* v_user_4719_; lean_object* v_group_4720_; lean_object* v_other_4721_; uint32_t v___x_4722_; uint32_t v___x_4723_; uint32_t v_u_4724_; uint32_t v___x_4725_; uint32_t v___x_4726_; uint32_t v_g_4727_; uint32_t v_o_4728_; uint32_t v___x_4729_; uint32_t v___x_4730_; 
v_user_4719_ = lean_ctor_get(v_acc_4718_, 0);
v_group_4720_ = lean_ctor_get(v_acc_4718_, 1);
v_other_4721_ = lean_ctor_get(v_acc_4718_, 2);
v___x_4722_ = l_IO_AccessRight_flags(v_user_4719_);
v___x_4723_ = 6;
v_u_4724_ = lean_uint32_shift_left(v___x_4722_, v___x_4723_);
v___x_4725_ = l_IO_AccessRight_flags(v_group_4720_);
v___x_4726_ = 3;
v_g_4727_ = lean_uint32_shift_left(v___x_4725_, v___x_4726_);
v_o_4728_ = l_IO_AccessRight_flags(v_other_4721_);
v___x_4729_ = lean_uint32_lor(v_g_4727_, v_o_4728_);
v___x_4730_ = lean_uint32_lor(v_u_4724_, v___x_4729_);
return v___x_4730_;
}
}
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object* v_acc_4731_){
_start:
{
uint32_t v_res_4732_; lean_object* v_r_4733_; 
v_res_4732_ = l_IO_FileRight_flags(v_acc_4731_);
lean_dec_ref(v_acc_4731_);
v_r_4733_ = lean_box_uint32(v_res_4732_);
return v_r_4733_;
}
}
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object* v_filename_4737_, lean_object* v_mode_4738_, lean_object* v_a_00___x40___internal___hyg_4739_){
_start:
{
uint32_t v_mode_boxed_4740_; lean_object* v_res_4741_; 
v_mode_boxed_4740_ = lean_unbox_uint32(v_mode_4738_);
lean_dec(v_mode_4738_);
v_res_4741_ = lean_chmod(v_filename_4737_, v_mode_boxed_4740_);
lean_dec_ref(v_filename_4737_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object* v_filename_4742_, lean_object* v_mode_4743_){
_start:
{
uint32_t v___x_4745_; lean_object* v___x_4746_; 
v___x_4745_ = l_IO_FileRight_flags(v_mode_4743_);
v___x_4746_ = lean_chmod(v_filename_4742_, v___x_4745_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object* v_filename_4747_, lean_object* v_mode_4748_, lean_object* v_a_4749_){
_start:
{
lean_object* v_res_4750_; 
v_res_4750_ = l_IO_setAccessRights(v_filename_4747_, v_mode_4748_);
lean_dec_ref(v_mode_4748_);
lean_dec_ref(v_filename_4747_);
return v_res_4750_;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object* v_00_u03b1_4751_, lean_object* v_mx_4752_){
_start:
{
lean_object* v___x_4754_; 
v___x_4754_ = lean_apply_1(v_mx_4752_, lean_box(0));
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object* v_00_u03b1_4755_, lean_object* v_mx_4756_, lean_object* v_s_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(v_00_u03b1_4755_, v_mx_4756_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg(lean_object* v_a_4761_){
_start:
{
lean_object* v___x_4763_; 
v___x_4763_ = lean_st_mk_ref(v_a_4761_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg___boxed(lean_object* v_a_4764_, lean_object* v_a_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l_IO_mkRef___redArg(v_a_4764_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object* v_00_u03b1_4767_, lean_object* v_a_4768_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = lean_st_mk_ref(v_a_4768_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___boxed(lean_object* v_00_u03b1_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l_IO_mkRef(v_00_u03b1_4771_, v_a_4772_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_new(){
_start:
{
uint8_t v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4776_ = 0;
v___x_4777_ = lean_box(v___x_4776_);
v___x_4778_ = lean_st_mk_ref(v___x_4777_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_new___boxed(lean_object* v_a_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l_IO_CancelToken_new();
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_set(lean_object* v_tk_4781_){
_start:
{
uint8_t v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4783_ = 1;
v___x_4784_ = lean_box(v___x_4783_);
v___x_4785_ = lean_st_ref_set(v_tk_4781_, v___x_4784_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_set___boxed(lean_object* v_tk_4786_, lean_object* v_a_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l_IO_CancelToken_set(v_tk_4786_);
lean_dec(v_tk_4786_);
return v_res_4788_;
}
}
LEAN_EXPORT uint8_t l_IO_CancelToken_isSet(lean_object* v_tk_4789_){
_start:
{
lean_object* v___x_4791_; uint8_t v___x_4792_; 
v___x_4791_ = lean_st_ref_get(v_tk_4789_);
v___x_4792_ = lean_unbox(v___x_4791_);
lean_dec(v___x_4791_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_isSet___boxed(lean_object* v_tk_4793_, lean_object* v_a_4794_){
_start:
{
uint8_t v_res_4795_; lean_object* v_r_4796_; 
v_res_4795_ = l_IO_CancelToken_isSet(v_tk_4793_);
lean_dec(v_tk_4793_);
v_r_4796_ = lean_box(v_res_4795_);
return v_r_4796_;
}
}
LEAN_EXPORT uint8_t lean_io_cancel_token_is_set(lean_object* v_tk_4797_){
_start:
{
lean_object* v___x_4799_; uint8_t v___x_4800_; 
v___x_4799_ = lean_st_ref_get(v_tk_4797_);
lean_dec(v_tk_4797_);
v___x_4800_ = lean_unbox(v___x_4799_);
lean_dec(v___x_4799_);
return v___x_4800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_CancelToken_isSetExport___boxed(lean_object* v_tk_4801_, lean_object* v_a_4802_){
_start:
{
uint8_t v_res_4803_; lean_object* v_r_4804_; 
v_res_4803_ = lean_io_cancel_token_is_set(v_tk_4801_);
v_r_4804_ = lean_box(v_res_4803_);
return v_r_4804_;
}
}
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object* v_h_4805_){
_start:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; 
lean_inc_n(v_h_4805_, 5);
v___x_4806_ = lean_alloc_closure((void*)(l_IO_FS_Handle_flush___boxed), 2, 1);
lean_closure_set(v___x_4806_, 0, v_h_4805_);
v___x_4807_ = lean_alloc_closure((void*)(l_IO_FS_Handle_read___boxed), 3, 1);
lean_closure_set(v___x_4807_, 0, v_h_4805_);
v___x_4808_ = lean_alloc_closure((void*)(l_IO_FS_Handle_write___boxed), 3, 1);
lean_closure_set(v___x_4808_, 0, v_h_4805_);
v___x_4809_ = lean_alloc_closure((void*)(l_IO_FS_Handle_getLine___boxed), 2, 1);
lean_closure_set(v___x_4809_, 0, v_h_4805_);
v___x_4810_ = lean_alloc_closure((void*)(l_IO_FS_Handle_putStr___boxed), 3, 1);
lean_closure_set(v___x_4810_, 0, v_h_4805_);
v___x_4811_ = lean_alloc_closure((void*)(l_IO_FS_Handle_isTty___boxed), 2, 1);
lean_closure_set(v___x_4811_, 0, v_h_4805_);
v___x_4812_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4812_, 0, v___x_4806_);
lean_ctor_set(v___x_4812_, 1, v___x_4807_);
lean_ctor_set(v___x_4812_, 2, v___x_4808_);
lean_ctor_set(v___x_4812_, 3, v___x_4809_);
lean_ctor_set(v___x_4812_, 4, v___x_4810_);
lean_ctor_set(v___x_4812_, 5, v___x_4811_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0(lean_object* v_r_4813_, size_t v_n_4814_){
_start:
{
lean_object* v___x_4816_; lean_object* v_data_4817_; lean_object* v_pos_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4832_; 
v___x_4816_ = lean_st_ref_take(v_r_4813_);
v_data_4817_ = lean_ctor_get(v___x_4816_, 0);
v_pos_4818_ = lean_ctor_get(v___x_4816_, 1);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4820_ = v___x_4816_;
v_isShared_4821_ = v_isSharedCheck_4832_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_pos_4818_);
lean_inc(v_data_4817_);
lean_dec(v___x_4816_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4832_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v_data_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4828_; 
v___x_4822_ = lean_usize_to_nat(v_n_4814_);
v___x_4823_ = lean_nat_add(v_pos_4818_, v___x_4822_);
lean_dec(v___x_4822_);
lean_inc(v_pos_4818_);
v_data_4824_ = l_ByteArray_extract(v_data_4817_, v_pos_4818_, v___x_4823_);
lean_dec(v___x_4823_);
v___x_4825_ = lean_byte_array_size(v_data_4824_);
v___x_4826_ = lean_nat_add(v_pos_4818_, v___x_4825_);
lean_dec(v_pos_4818_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 1, v___x_4826_);
v___x_4828_ = v___x_4820_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_data_4817_);
lean_ctor_set(v_reuseFailAlloc_4831_, 1, v___x_4826_);
v___x_4828_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___x_4829_ = lean_st_ref_set(v_r_4813_, v___x_4828_);
v___x_4830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4830_, 0, v_data_4824_);
return v___x_4830_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0___boxed(lean_object* v_r_4833_, lean_object* v_n_4834_, lean_object* v___y_4835_){
_start:
{
size_t v_n_boxed_4836_; lean_object* v_res_4837_; 
v_n_boxed_4836_ = lean_unbox_usize(v_n_4834_);
lean_dec(v_n_4834_);
v_res_4837_ = l_IO_FS_Stream_ofBuffer___lam__0(v_r_4833_, v_n_boxed_4836_);
lean_dec(v_r_4833_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1(lean_object* v_r_4838_, lean_object* v_data_4839_){
_start:
{
lean_object* v___x_4841_; lean_object* v_data_4842_; lean_object* v_pos_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4857_; 
v___x_4841_ = lean_st_ref_take(v_r_4838_);
v_data_4842_ = lean_ctor_get(v___x_4841_, 0);
v_pos_4843_ = lean_ctor_get(v___x_4841_, 1);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4845_ = v___x_4841_;
v_isShared_4846_ = v_isSharedCheck_4857_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_pos_4843_);
lean_inc(v_data_4842_);
lean_dec(v___x_4841_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4857_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; uint8_t v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4853_; 
v___x_4847_ = lean_unsigned_to_nat(0u);
v___x_4848_ = lean_byte_array_size(v_data_4839_);
v___x_4849_ = 0;
lean_inc(v_pos_4843_);
v___x_4850_ = lean_byte_array_copy_slice(v_data_4839_, v___x_4847_, v_data_4842_, v_pos_4843_, v___x_4848_, v___x_4849_);
v___x_4851_ = lean_nat_add(v_pos_4843_, v___x_4848_);
lean_dec(v_pos_4843_);
if (v_isShared_4846_ == 0)
{
lean_ctor_set(v___x_4845_, 1, v___x_4851_);
lean_ctor_set(v___x_4845_, 0, v___x_4850_);
v___x_4853_ = v___x_4845_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v___x_4850_);
lean_ctor_set(v_reuseFailAlloc_4856_, 1, v___x_4851_);
v___x_4853_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4854_ = lean_st_ref_set(v_r_4838_, v___x_4853_);
v___x_4855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4854_);
return v___x_4855_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1___boxed(lean_object* v_r_4858_, lean_object* v_data_4859_, lean_object* v___y_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l_IO_FS_Stream_ofBuffer___lam__1(v_r_4858_, v_data_4859_);
lean_dec_ref(v_data_4859_);
lean_dec(v_r_4858_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2(lean_object* v_r_4862_, lean_object* v_s_4863_){
_start:
{
lean_object* v___x_4865_; lean_object* v_data_4866_; lean_object* v_pos_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4882_; 
v___x_4865_ = lean_st_ref_take(v_r_4862_);
v_data_4866_ = lean_ctor_get(v___x_4865_, 0);
v_pos_4867_ = lean_ctor_get(v___x_4865_, 1);
v_isSharedCheck_4882_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4869_ = v___x_4865_;
v_isShared_4870_ = v_isSharedCheck_4882_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_pos_4867_);
lean_inc(v_data_4866_);
lean_dec(v___x_4865_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4882_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v_data_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; uint8_t v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4878_; 
v_data_4871_ = lean_string_to_utf8(v_s_4863_);
v___x_4872_ = lean_unsigned_to_nat(0u);
v___x_4873_ = lean_byte_array_size(v_data_4871_);
v___x_4874_ = 0;
lean_inc(v_pos_4867_);
v___x_4875_ = lean_byte_array_copy_slice(v_data_4871_, v___x_4872_, v_data_4866_, v_pos_4867_, v___x_4873_, v___x_4874_);
lean_dec_ref(v_data_4871_);
v___x_4876_ = lean_nat_add(v_pos_4867_, v___x_4873_);
lean_dec(v_pos_4867_);
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 1, v___x_4876_);
lean_ctor_set(v___x_4869_, 0, v___x_4875_);
v___x_4878_ = v___x_4869_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v___x_4875_);
lean_ctor_set(v_reuseFailAlloc_4881_, 1, v___x_4876_);
v___x_4878_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4879_ = lean_st_ref_set(v_r_4862_, v___x_4878_);
v___x_4880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4879_);
return v___x_4880_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2___boxed(lean_object* v_r_4883_, lean_object* v_s_4884_, lean_object* v___y_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l_IO_FS_Stream_ofBuffer___lam__2(v_r_4883_, v_s_4884_);
lean_dec_ref(v_s_4884_);
lean_dec(v_r_4883_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(lean_object* v_a_4887_, lean_object* v_i_4888_){
_start:
{
uint8_t v___y_4890_; lean_object* v___x_4895_; uint8_t v___x_4896_; 
v___x_4895_ = lean_byte_array_size(v_a_4887_);
v___x_4896_ = lean_nat_dec_lt(v_i_4888_, v___x_4895_);
if (v___x_4896_ == 0)
{
lean_object* v___x_4897_; 
lean_dec(v_i_4888_);
v___x_4897_ = lean_box(0);
return v___x_4897_;
}
else
{
uint8_t v___x_4898_; uint8_t v___x_4899_; uint8_t v___x_4900_; 
v___x_4898_ = lean_byte_array_fget(v_a_4887_, v_i_4888_);
v___x_4899_ = 0;
v___x_4900_ = lean_uint8_dec_eq(v___x_4898_, v___x_4899_);
if (v___x_4900_ == 0)
{
uint8_t v___x_4901_; uint8_t v___x_4902_; 
v___x_4901_ = 10;
v___x_4902_ = lean_uint8_dec_eq(v___x_4898_, v___x_4901_);
v___y_4890_ = v___x_4902_;
goto v___jp_4889_;
}
else
{
v___y_4890_ = v___x_4900_;
goto v___jp_4889_;
}
}
v___jp_4889_:
{
if (v___y_4890_ == 0)
{
lean_object* v___x_4891_; lean_object* v___x_4892_; 
v___x_4891_ = lean_unsigned_to_nat(1u);
v___x_4892_ = lean_nat_add(v_i_4888_, v___x_4891_);
lean_dec(v_i_4888_);
v_i_4888_ = v___x_4892_;
goto _start;
}
else
{
lean_object* v___x_4894_; 
v___x_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4894_, 0, v_i_4888_);
return v___x_4894_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0___boxed(lean_object* v_a_4903_, lean_object* v_i_4904_){
_start:
{
lean_object* v_res_4905_; 
v_res_4905_ = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(v_a_4903_, v_i_4904_);
lean_dec_ref(v_a_4903_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3(lean_object* v_r_4909_){
_start:
{
lean_object* v___x_4911_; lean_object* v_data_4912_; lean_object* v_pos_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4937_; 
v___x_4911_ = lean_st_ref_take(v_r_4909_);
v_data_4912_ = lean_ctor_get(v___x_4911_, 0);
v_pos_4913_ = lean_ctor_get(v___x_4911_, 1);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4915_ = v___x_4911_;
v_isShared_4916_ = v_isSharedCheck_4937_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_pos_4913_);
lean_inc(v_data_4912_);
lean_dec(v___x_4911_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4937_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___y_4918_; lean_object* v___x_4929_; 
lean_inc(v_pos_4913_);
v___x_4929_ = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(v_data_4912_, v_pos_4913_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v___x_4930_; 
v___x_4930_ = lean_byte_array_size(v_data_4912_);
v___y_4918_ = v___x_4930_;
goto v___jp_4917_;
}
else
{
lean_object* v_val_4931_; uint8_t v___x_4932_; uint8_t v___x_4933_; uint8_t v___x_4934_; 
v_val_4931_ = lean_ctor_get(v___x_4929_, 0);
lean_inc(v_val_4931_);
lean_dec_ref(v___x_4929_);
v___x_4932_ = lean_byte_array_get(v_data_4912_, v_val_4931_);
v___x_4933_ = 0;
v___x_4934_ = lean_uint8_dec_eq(v___x_4932_, v___x_4933_);
if (v___x_4934_ == 0)
{
lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4935_ = lean_unsigned_to_nat(1u);
v___x_4936_ = lean_nat_add(v_val_4931_, v___x_4935_);
lean_dec(v_val_4931_);
v___y_4918_ = v___x_4936_;
goto v___jp_4917_;
}
else
{
v___y_4918_ = v_val_4931_;
goto v___jp_4917_;
}
}
v___jp_4917_:
{
lean_object* v___x_4919_; lean_object* v___x_4921_; 
v___x_4919_ = l_ByteArray_extract(v_data_4912_, v_pos_4913_, v___y_4918_);
if (v_isShared_4916_ == 0)
{
lean_ctor_set(v___x_4915_, 1, v___y_4918_);
v___x_4921_ = v___x_4915_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_data_4912_);
lean_ctor_set(v_reuseFailAlloc_4928_, 1, v___y_4918_);
v___x_4921_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
lean_object* v___x_4922_; uint8_t v___x_4923_; 
v___x_4922_ = lean_st_ref_set(v_r_4909_, v___x_4921_);
v___x_4923_ = lean_string_validate_utf8(v___x_4919_);
if (v___x_4923_ == 0)
{
lean_object* v___x_4924_; lean_object* v___x_4925_; 
lean_dec_ref(v___x_4919_);
v___x_4924_ = ((lean_object*)(l_IO_FS_Stream_ofBuffer___lam__3___closed__1));
v___x_4925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4924_);
return v___x_4925_;
}
else
{
lean_object* v___x_4926_; lean_object* v___x_4927_; 
v___x_4926_ = lean_string_from_utf8_unchecked(v___x_4919_);
v___x_4927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4926_);
return v___x_4927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3___boxed(lean_object* v_r_4938_, lean_object* v___y_4939_){
_start:
{
lean_object* v_res_4940_; 
v_res_4940_ = l_IO_FS_Stream_ofBuffer___lam__3(v_r_4938_);
lean_dec(v_r_4938_);
return v_res_4940_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4(lean_object* v___x_4941_){
_start:
{
lean_object* v___x_4943_; 
v___x_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4943_, 0, v___x_4941_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4___boxed(lean_object* v___x_4944_, lean_object* v___y_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_IO_FS_Stream_ofBuffer___lam__4(v___x_4944_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object* v_r_4949_){
_start:
{
lean_object* v___f_4950_; lean_object* v___f_4951_; lean_object* v___f_4952_; lean_object* v___f_4953_; lean_object* v___f_4954_; lean_object* v___f_4955_; lean_object* v___x_4956_; 
lean_inc_n(v_r_4949_, 3);
v___f_4950_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4950_, 0, v_r_4949_);
v___f_4951_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4951_, 0, v_r_4949_);
v___f_4952_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4952_, 0, v_r_4949_);
v___f_4953_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__3___boxed), 2, 1);
lean_closure_set(v___f_4953_, 0, v_r_4949_);
v___f_4954_ = ((lean_object*)(l_IO_FS_Stream_ofBuffer___closed__0));
v___f_4955_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___closed__5));
v___x_4956_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4956_, 0, v___f_4954_);
lean_ctor_set(v___x_4956_, 1, v___f_4950_);
lean_ctor_set(v___x_4956_, 2, v___f_4951_);
lean_ctor_set(v___x_4956_, 3, v___f_4953_);
lean_ctor_set(v___x_4956_, 4, v___f_4952_);
lean_ctor_set(v___x_4956_, 5, v___f_4955_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(lean_object* v_s_4959_, lean_object* v_acc_4960_){
_start:
{
lean_object* v_read_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
v_read_4962_ = lean_ctor_get(v_s_4959_, 1);
v___x_4963_ = ((lean_object*)(l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1));
lean_inc_ref(v_read_4962_);
v___x_4964_ = lean_apply_2(v_read_4962_, v___x_4963_, lean_box(0));
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v_a_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4978_; 
v_a_4965_ = lean_ctor_get(v___x_4964_, 0);
v_isSharedCheck_4978_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_4978_ == 0)
{
v___x_4967_ = v___x_4964_;
v_isShared_4968_ = v_isSharedCheck_4978_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_a_4965_);
lean_dec(v___x_4964_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4978_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
uint8_t v___x_4969_; 
v___x_4969_ = l_ByteArray_isEmpty(v_a_4965_);
if (v___x_4969_ == 0)
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
lean_del_object(v___x_4967_);
v___x_4970_ = lean_unsigned_to_nat(0u);
v___x_4971_ = lean_byte_array_size(v_acc_4960_);
v___x_4972_ = lean_byte_array_size(v_a_4965_);
v___x_4973_ = lean_byte_array_copy_slice(v_a_4965_, v___x_4970_, v_acc_4960_, v___x_4971_, v___x_4972_, v___x_4969_);
lean_dec(v_a_4965_);
v_acc_4960_ = v___x_4973_;
goto _start;
}
else
{
lean_object* v___x_4976_; 
lean_dec(v_a_4965_);
lean_dec_ref(v_s_4959_);
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 0, v_acc_4960_);
v___x_4976_ = v___x_4967_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v_acc_4960_);
v___x_4976_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
return v___x_4976_;
}
}
}
}
else
{
lean_dec_ref(v_acc_4960_);
lean_dec_ref(v_s_4959_);
return v___x_4964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed(lean_object* v_s_4979_, lean_object* v_acc_4980_, lean_object* v_a_4981_){
_start:
{
lean_object* v_res_4982_; 
v_res_4982_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4979_, v_acc_4980_);
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto(lean_object* v_s_4983_, lean_object* v_buf_4984_){
_start:
{
lean_object* v___x_4986_; 
v___x_4986_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4983_, v_buf_4984_);
return v___x_4986_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto___boxed(lean_object* v_s_4987_, lean_object* v_buf_4988_, lean_object* v_a_4989_){
_start:
{
lean_object* v_res_4990_; 
v_res_4990_ = l_IO_FS_Stream_readBinToEndInto(v_s_4987_, v_buf_4988_);
return v_res_4990_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd(lean_object* v_s_4991_){
_start:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4993_ = l_ByteArray_empty;
v___x_4994_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4991_, v___x_4993_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd___boxed(lean_object* v_s_4995_, lean_object* v_a_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l_IO_FS_Stream_readBinToEnd(v_s_4995_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd(lean_object* v_s_5001_){
_start:
{
lean_object* v___x_5003_; 
v___x_5003_ = l_IO_FS_Stream_readBinToEnd(v_s_5001_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5017_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5006_ = v___x_5003_;
v_isShared_5007_ = v_isSharedCheck_5017_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_5003_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5017_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
uint8_t v___x_5008_; 
v___x_5008_ = lean_string_validate_utf8(v_a_5004_);
if (v___x_5008_ == 0)
{
lean_object* v___x_5009_; lean_object* v___x_5011_; 
lean_dec(v_a_5004_);
v___x_5009_ = ((lean_object*)(l_IO_FS_Stream_readToEnd___closed__1));
if (v_isShared_5007_ == 0)
{
lean_ctor_set_tag(v___x_5006_, 1);
lean_ctor_set(v___x_5006_, 0, v___x_5009_);
v___x_5011_ = v___x_5006_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v___x_5009_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
else
{
lean_object* v___x_5013_; lean_object* v___x_5015_; 
v___x_5013_ = lean_string_from_utf8_unchecked(v_a_5004_);
if (v_isShared_5007_ == 0)
{
lean_ctor_set(v___x_5006_, 0, v___x_5013_);
v___x_5015_ = v___x_5006_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5013_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
v_a_5018_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_5003_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5003_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd___boxed(lean_object* v_s_5026_, lean_object* v_a_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l_IO_FS_Stream_readToEnd(v_s_5026_);
return v_res_5028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read(lean_object* v_s_5029_, lean_object* v_lines_5030_){
_start:
{
lean_object* v_getLine_5032_; lean_object* v___x_5033_; 
v_getLine_5032_ = lean_ctor_get(v_s_5029_, 3);
lean_inc_ref(v_getLine_5032_);
v___x_5033_ = lean_apply_1(v_getLine_5032_, lean_box(0));
if (lean_obj_tag(v___x_5033_) == 0)
{
lean_object* v_a_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5089_; 
v_a_5034_ = lean_ctor_get(v___x_5033_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5033_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5036_ = v___x_5033_;
v_isShared_5037_ = v_isSharedCheck_5089_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_a_5034_);
lean_dec(v___x_5033_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5089_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___y_5039_; lean_object* v___y_5043_; lean_object* v___y_5044_; lean_object* v___y_5045_; uint32_t v___y_5046_; uint32_t v___y_5054_; lean_object* v___x_5076_; lean_object* v___x_5077_; uint8_t v___x_5078_; 
v___x_5076_ = lean_string_length(v_a_5034_);
v___x_5077_ = lean_unsigned_to_nat(0u);
v___x_5078_ = lean_nat_dec_eq(v___x_5076_, v___x_5077_);
if (v___x_5078_ == 0)
{
lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___x_5079_ = lean_string_utf8_byte_size(v_a_5034_);
lean_inc(v_a_5034_);
v___x_5080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5080_, 0, v_a_5034_);
lean_ctor_set(v___x_5080_, 1, v___x_5077_);
lean_ctor_set(v___x_5080_, 2, v___x_5079_);
v___x_5081_ = l_String_Slice_Pos_prev_x3f(v___x_5080_, v___x_5079_);
if (lean_obj_tag(v___x_5081_) == 0)
{
uint32_t v___x_5082_; 
lean_dec_ref(v___x_5080_);
v___x_5082_ = 65;
v___y_5054_ = v___x_5082_;
goto v___jp_5053_;
}
else
{
lean_object* v_val_5083_; lean_object* v___x_5084_; 
v_val_5083_ = lean_ctor_get(v___x_5081_, 0);
lean_inc(v_val_5083_);
lean_dec_ref(v___x_5081_);
v___x_5084_ = l_String_Slice_Pos_get_x3f(v___x_5080_, v_val_5083_);
lean_dec(v_val_5083_);
lean_dec_ref(v___x_5080_);
if (lean_obj_tag(v___x_5084_) == 0)
{
uint32_t v___x_5085_; 
v___x_5085_ = 65;
v___y_5054_ = v___x_5085_;
goto v___jp_5053_;
}
else
{
lean_object* v_val_5086_; uint32_t v___x_5087_; 
v_val_5086_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_val_5086_);
lean_dec_ref(v___x_5084_);
v___x_5087_ = lean_unbox_uint32(v_val_5086_);
lean_dec(v_val_5086_);
v___y_5054_ = v___x_5087_;
goto v___jp_5053_;
}
}
}
else
{
lean_object* v___x_5088_; 
lean_del_object(v___x_5036_);
lean_dec(v_a_5034_);
lean_dec_ref(v_s_5029_);
v___x_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5088_, 0, v_lines_5030_);
return v___x_5088_;
}
v___jp_5038_:
{
lean_object* v___x_5040_; 
v___x_5040_ = lean_array_push(v_lines_5030_, v___y_5039_);
v_lines_5030_ = v___x_5040_;
goto _start;
}
v___jp_5042_:
{
uint32_t v___x_5047_; uint8_t v___x_5048_; 
v___x_5047_ = 13;
v___x_5048_ = lean_uint32_dec_eq(v___y_5046_, v___x_5047_);
if (v___x_5048_ == 0)
{
lean_dec(v___y_5045_);
lean_dec(v___y_5043_);
v___y_5039_ = v___y_5044_;
goto v___jp_5038_;
}
else
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; 
v___x_5049_ = lean_string_utf8_byte_size(v___y_5044_);
lean_inc(v___y_5043_);
lean_inc_ref(v___y_5044_);
v___x_5050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5050_, 0, v___y_5044_);
lean_ctor_set(v___x_5050_, 1, v___y_5043_);
lean_ctor_set(v___x_5050_, 2, v___x_5049_);
v___x_5051_ = l_String_Slice_Pos_prevn(v___x_5050_, v___x_5049_, v___y_5045_);
lean_dec_ref(v___x_5050_);
v___x_5052_ = lean_string_utf8_extract(v___y_5044_, v___y_5043_, v___x_5051_);
lean_dec(v___x_5051_);
lean_dec(v___y_5043_);
lean_dec_ref(v___y_5044_);
v___y_5039_ = v___x_5052_;
goto v___jp_5038_;
}
}
v___jp_5053_:
{
uint32_t v___x_5055_; uint8_t v___x_5056_; 
v___x_5055_ = 10;
v___x_5056_ = lean_uint32_dec_eq(v___y_5054_, v___x_5055_);
if (v___x_5056_ == 0)
{
lean_object* v___x_5057_; lean_object* v___x_5059_; 
lean_dec_ref(v_s_5029_);
v___x_5057_ = lean_array_push(v_lines_5030_, v_a_5034_);
if (v_isShared_5037_ == 0)
{
lean_ctor_set(v___x_5036_, 0, v___x_5057_);
v___x_5059_ = v___x_5036_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5057_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
return v___x_5059_;
}
}
else
{
lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; 
lean_del_object(v___x_5036_);
v___x_5061_ = lean_unsigned_to_nat(1u);
v___x_5062_ = lean_unsigned_to_nat(0u);
v___x_5063_ = lean_string_utf8_byte_size(v_a_5034_);
lean_inc(v_a_5034_);
v___x_5064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5064_, 0, v_a_5034_);
lean_ctor_set(v___x_5064_, 1, v___x_5062_);
lean_ctor_set(v___x_5064_, 2, v___x_5063_);
v___x_5065_ = l_String_Slice_Pos_prevn(v___x_5064_, v___x_5063_, v___x_5061_);
lean_dec_ref(v___x_5064_);
v___x_5066_ = lean_string_utf8_extract(v_a_5034_, v___x_5062_, v___x_5065_);
lean_dec(v___x_5065_);
lean_dec(v_a_5034_);
v___x_5067_ = lean_string_utf8_byte_size(v___x_5066_);
lean_inc_ref(v___x_5066_);
v___x_5068_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5066_);
lean_ctor_set(v___x_5068_, 1, v___x_5062_);
lean_ctor_set(v___x_5068_, 2, v___x_5067_);
v___x_5069_ = l_String_Slice_Pos_prev_x3f(v___x_5068_, v___x_5067_);
if (lean_obj_tag(v___x_5069_) == 0)
{
uint32_t v___x_5070_; 
lean_dec_ref(v___x_5068_);
v___x_5070_ = 65;
v___y_5043_ = v___x_5062_;
v___y_5044_ = v___x_5066_;
v___y_5045_ = v___x_5061_;
v___y_5046_ = v___x_5070_;
goto v___jp_5042_;
}
else
{
lean_object* v_val_5071_; lean_object* v___x_5072_; 
v_val_5071_ = lean_ctor_get(v___x_5069_, 0);
lean_inc(v_val_5071_);
lean_dec_ref(v___x_5069_);
v___x_5072_ = l_String_Slice_Pos_get_x3f(v___x_5068_, v_val_5071_);
lean_dec(v_val_5071_);
lean_dec_ref(v___x_5068_);
if (lean_obj_tag(v___x_5072_) == 0)
{
uint32_t v___x_5073_; 
v___x_5073_ = 65;
v___y_5043_ = v___x_5062_;
v___y_5044_ = v___x_5066_;
v___y_5045_ = v___x_5061_;
v___y_5046_ = v___x_5073_;
goto v___jp_5042_;
}
else
{
lean_object* v_val_5074_; uint32_t v___x_5075_; 
v_val_5074_ = lean_ctor_get(v___x_5072_, 0);
lean_inc(v_val_5074_);
lean_dec_ref(v___x_5072_);
v___x_5075_ = lean_unbox_uint32(v_val_5074_);
lean_dec(v_val_5074_);
v___y_5043_ = v___x_5062_;
v___y_5044_ = v___x_5066_;
v___y_5045_ = v___x_5061_;
v___y_5046_ = v___x_5075_;
goto v___jp_5042_;
}
}
}
}
}
}
else
{
lean_object* v_a_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5097_; 
lean_dec_ref(v_lines_5030_);
lean_dec_ref(v_s_5029_);
v_a_5090_ = lean_ctor_get(v___x_5033_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v___x_5033_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5092_ = v___x_5033_;
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_a_5090_);
lean_dec(v___x_5033_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5095_; 
if (v_isShared_5093_ == 0)
{
v___x_5095_ = v___x_5092_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5090_);
v___x_5095_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
return v___x_5095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read___boxed(lean_object* v_s_5098_, lean_object* v_lines_5099_, lean_object* v_a_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_5098_, v_lines_5099_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines(lean_object* v_s_5102_){
_start:
{
lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5104_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_5105_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_5102_, v___x_5104_);
return v___x_5105_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines___boxed(lean_object* v_s_5106_, lean_object* v_a_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l_IO_FS_Stream_lines(v_s_5106_);
return v_res_5108_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0(lean_object* v_bOut_5109_){
_start:
{
lean_object* v___x_5111_; 
v___x_5111_ = lean_st_ref_get(v_bOut_5109_);
return v___x_5111_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed(lean_object* v_bOut_5112_, lean_object* v___y_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l_IO_FS_withIsolatedStreams___redArg___lam__0(v_bOut_5112_);
lean_dec(v_bOut_5112_);
return v_res_5114_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; 
v___x_5119_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3));
v___x_5120_ = lean_unsigned_to_nat(46u);
v___x_5121_ = lean_unsigned_to_nat(193u);
v___x_5122_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2));
v___x_5123_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1));
v___x_5124_ = l_mkPanicMessageWithDecl(v___x_5123_, v___x_5122_, v___x_5121_, v___x_5120_, v___x_5119_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1(lean_object* v_r_5125_, lean_object* v_toPure_5126_, lean_object* v_bOut_5127_){
_start:
{
lean_object* v___y_5129_; lean_object* v_data_5132_; uint8_t v___x_5133_; 
v_data_5132_ = lean_ctor_get(v_bOut_5127_, 0);
lean_inc_ref(v_data_5132_);
lean_dec_ref(v_bOut_5127_);
v___x_5133_ = lean_string_validate_utf8(v_data_5132_);
if (v___x_5133_ == 0)
{
lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; 
lean_dec_ref(v_data_5132_);
v___x_5134_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0));
v___x_5135_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4, &l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4_once, _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4);
v___x_5136_ = l_panic___redArg(v___x_5134_, v___x_5135_);
v___y_5129_ = v___x_5136_;
goto v___jp_5128_;
}
else
{
lean_object* v___x_5137_; 
v___x_5137_ = lean_string_from_utf8_unchecked(v_data_5132_);
v___y_5129_ = v___x_5137_;
goto v___jp_5128_;
}
v___jp_5128_:
{
lean_object* v___x_5130_; lean_object* v___x_5131_; 
v___x_5130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5130_, 0, v___y_5129_);
lean_ctor_set(v___x_5130_, 1, v_r_5125_);
v___x_5131_ = lean_apply_2(v_toPure_5126_, lean_box(0), v___x_5130_);
return v___x_5131_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__2(lean_object* v_toPure_5138_, lean_object* v_inst_5139_, lean_object* v___f_5140_, lean_object* v_toBind_5141_, lean_object* v_r_5142_){
_start:
{
lean_object* v___f_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; 
v___f_5143_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5143_, 0, v_r_5142_);
lean_closure_set(v___f_5143_, 1, v_toPure_5138_);
v___x_5144_ = lean_apply_2(v_inst_5139_, lean_box(0), v___f_5140_);
v___x_5145_ = lean_apply_4(v_toBind_5141_, lean_box(0), lean_box(0), v___x_5144_, v___f_5143_);
return v___x_5145_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3(lean_object* v_toPure_5146_, lean_object* v_inst_5147_, lean_object* v_toBind_5148_, lean_object* v_bIn_5149_, lean_object* v_inst_5150_, lean_object* v_inst_5151_, uint8_t v_isolateStderr_5152_, lean_object* v_x_5153_, lean_object* v_bOut_5154_){
_start:
{
lean_object* v___f_5155_; lean_object* v___f_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___y_5160_; 
lean_inc(v_bOut_5154_);
v___f_5155_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5155_, 0, v_bOut_5154_);
lean_inc(v_toBind_5148_);
lean_inc(v_inst_5147_);
v___f_5156_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__2), 5, 4);
lean_closure_set(v___f_5156_, 0, v_toPure_5146_);
lean_closure_set(v___f_5156_, 1, v_inst_5147_);
lean_closure_set(v___f_5156_, 2, v___f_5155_);
lean_closure_set(v___f_5156_, 3, v_toBind_5148_);
v___x_5157_ = l_IO_FS_Stream_ofBuffer(v_bIn_5149_);
v___x_5158_ = l_IO_FS_Stream_ofBuffer(v_bOut_5154_);
if (v_isolateStderr_5152_ == 0)
{
v___y_5160_ = v_x_5153_;
goto v___jp_5159_;
}
else
{
lean_object* v___x_5164_; 
lean_inc_ref(v___x_5158_);
lean_inc(v_inst_5147_);
lean_inc(v_inst_5151_);
lean_inc_ref(v_inst_5150_);
v___x_5164_ = l_IO_withStderr___redArg(v_inst_5150_, v_inst_5151_, v_inst_5147_, v___x_5158_, v_x_5153_);
v___y_5160_ = v___x_5164_;
goto v___jp_5159_;
}
v___jp_5159_:
{
lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; 
lean_inc(v_inst_5147_);
lean_inc(v_inst_5151_);
lean_inc_ref(v_inst_5150_);
v___x_5161_ = l_IO_withStdout___redArg(v_inst_5150_, v_inst_5151_, v_inst_5147_, v___x_5158_, v___y_5160_);
v___x_5162_ = l_IO_withStdin___redArg(v_inst_5150_, v_inst_5151_, v_inst_5147_, v___x_5157_, v___x_5161_);
v___x_5163_ = lean_apply_4(v_toBind_5148_, lean_box(0), lean_box(0), v___x_5162_, v___f_5156_);
return v___x_5163_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed(lean_object* v_toPure_5165_, lean_object* v_inst_5166_, lean_object* v_toBind_5167_, lean_object* v_bIn_5168_, lean_object* v_inst_5169_, lean_object* v_inst_5170_, lean_object* v_isolateStderr_5171_, lean_object* v_x_5172_, lean_object* v_bOut_5173_){
_start:
{
uint8_t v_isolateStderr_boxed_5174_; lean_object* v_res_5175_; 
v_isolateStderr_boxed_5174_ = lean_unbox(v_isolateStderr_5171_);
v_res_5175_ = l_IO_FS_withIsolatedStreams___redArg___lam__3(v_toPure_5165_, v_inst_5166_, v_toBind_5167_, v_bIn_5168_, v_inst_5169_, v_inst_5170_, v_isolateStderr_boxed_5174_, v_x_5172_, v_bOut_5173_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4(lean_object* v_toPure_5176_, lean_object* v_inst_5177_, lean_object* v_toBind_5178_, lean_object* v_inst_5179_, lean_object* v_inst_5180_, uint8_t v_isolateStderr_5181_, lean_object* v_x_5182_, lean_object* v___x_5183_, lean_object* v_bIn_5184_){
_start:
{
lean_object* v___x_5185_; lean_object* v___f_5186_; lean_object* v___x_5187_; 
v___x_5185_ = lean_box(v_isolateStderr_5181_);
lean_inc(v_toBind_5178_);
v___f_5186_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_5186_, 0, v_toPure_5176_);
lean_closure_set(v___f_5186_, 1, v_inst_5177_);
lean_closure_set(v___f_5186_, 2, v_toBind_5178_);
lean_closure_set(v___f_5186_, 3, v_bIn_5184_);
lean_closure_set(v___f_5186_, 4, v_inst_5179_);
lean_closure_set(v___f_5186_, 5, v_inst_5180_);
lean_closure_set(v___f_5186_, 6, v___x_5185_);
lean_closure_set(v___f_5186_, 7, v_x_5182_);
v___x_5187_ = lean_apply_4(v_toBind_5178_, lean_box(0), lean_box(0), v___x_5183_, v___f_5186_);
return v___x_5187_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed(lean_object* v_toPure_5188_, lean_object* v_inst_5189_, lean_object* v_toBind_5190_, lean_object* v_inst_5191_, lean_object* v_inst_5192_, lean_object* v_isolateStderr_5193_, lean_object* v_x_5194_, lean_object* v___x_5195_, lean_object* v_bIn_5196_){
_start:
{
uint8_t v_isolateStderr_boxed_5197_; lean_object* v_res_5198_; 
v_isolateStderr_boxed_5197_ = lean_unbox(v_isolateStderr_5193_);
v_res_5198_ = l_IO_FS_withIsolatedStreams___redArg___lam__4(v_toPure_5188_, v_inst_5189_, v_toBind_5190_, v_inst_5191_, v_inst_5192_, v_isolateStderr_boxed_5197_, v_x_5194_, v___x_5195_, v_bIn_5196_);
return v_res_5198_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__0(void){
_start:
{
lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; 
v___x_5199_ = lean_unsigned_to_nat(0u);
v___x_5200_ = l_ByteArray_empty;
v___x_5201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5200_);
lean_ctor_set(v___x_5201_, 1, v___x_5199_);
return v___x_5201_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__1(void){
_start:
{
lean_object* v___x_5202_; lean_object* v___x_5203_; 
v___x_5202_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___closed__0, &l_IO_FS_withIsolatedStreams___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___redArg___closed__0);
v___x_5203_ = lean_alloc_closure((void*)(l_IO_mkRef___boxed), 3, 2);
lean_closure_set(v___x_5203_, 0, lean_box(0));
lean_closure_set(v___x_5203_, 1, v___x_5202_);
return v___x_5203_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object* v_inst_5204_, lean_object* v_inst_5205_, lean_object* v_inst_5206_, lean_object* v_x_5207_, uint8_t v_isolateStderr_5208_){
_start:
{
lean_object* v_toApplicative_5209_; lean_object* v_toBind_5210_; lean_object* v_toPure_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___f_5215_; lean_object* v___x_5216_; 
v_toApplicative_5209_ = lean_ctor_get(v_inst_5204_, 0);
v_toBind_5210_ = lean_ctor_get(v_inst_5204_, 1);
lean_inc_n(v_toBind_5210_, 2);
v_toPure_5211_ = lean_ctor_get(v_toApplicative_5209_, 1);
lean_inc(v_toPure_5211_);
v___x_5212_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___closed__1, &l_IO_FS_withIsolatedStreams___redArg___closed__1_once, _init_l_IO_FS_withIsolatedStreams___redArg___closed__1);
lean_inc(v_inst_5206_);
v___x_5213_ = lean_apply_2(v_inst_5206_, lean_box(0), v___x_5212_);
v___x_5214_ = lean_box(v_isolateStderr_5208_);
lean_inc(v___x_5213_);
v___f_5215_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_5215_, 0, v_toPure_5211_);
lean_closure_set(v___f_5215_, 1, v_inst_5206_);
lean_closure_set(v___f_5215_, 2, v_toBind_5210_);
lean_closure_set(v___f_5215_, 3, v_inst_5204_);
lean_closure_set(v___f_5215_, 4, v_inst_5205_);
lean_closure_set(v___f_5215_, 5, v___x_5214_);
lean_closure_set(v___f_5215_, 6, v_x_5207_);
lean_closure_set(v___f_5215_, 7, v___x_5213_);
v___x_5216_ = lean_apply_4(v_toBind_5210_, lean_box(0), lean_box(0), v___x_5213_, v___f_5215_);
return v___x_5216_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___boxed(lean_object* v_inst_5217_, lean_object* v_inst_5218_, lean_object* v_inst_5219_, lean_object* v_x_5220_, lean_object* v_isolateStderr_5221_){
_start:
{
uint8_t v_isolateStderr_boxed_5222_; lean_object* v_res_5223_; 
v_isolateStderr_boxed_5222_ = lean_unbox(v_isolateStderr_5221_);
v_res_5223_ = l_IO_FS_withIsolatedStreams___redArg(v_inst_5217_, v_inst_5218_, v_inst_5219_, v_x_5220_, v_isolateStderr_boxed_5222_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object* v_m_5224_, lean_object* v_00_u03b1_5225_, lean_object* v_inst_5226_, lean_object* v_inst_5227_, lean_object* v_inst_5228_, lean_object* v_x_5229_, uint8_t v_isolateStderr_5230_){
_start:
{
lean_object* v___x_5231_; 
v___x_5231_ = l_IO_FS_withIsolatedStreams___redArg(v_inst_5226_, v_inst_5227_, v_inst_5228_, v_x_5229_, v_isolateStderr_5230_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___boxed(lean_object* v_m_5232_, lean_object* v_00_u03b1_5233_, lean_object* v_inst_5234_, lean_object* v_inst_5235_, lean_object* v_inst_5236_, lean_object* v_x_5237_, lean_object* v_isolateStderr_5238_){
_start:
{
uint8_t v_isolateStderr_boxed_5239_; lean_object* v_res_5240_; 
v_isolateStderr_boxed_5239_ = lean_unbox(v_isolateStderr_5238_);
v_res_5240_ = l_IO_FS_withIsolatedStreams(v_m_5232_, v_00_u03b1_5233_, v_inst_5234_, v_inst_5235_, v_inst_5236_, v_x_5237_, v_isolateStderr_boxed_5239_);
return v_res_5240_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9(void){
_start:
{
lean_object* v___x_5297_; lean_object* v___x_5298_; 
v___x_5297_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0));
v___x_5298_ = l_String_toRawSubstring_x27(v___x_5297_);
return v___x_5298_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17(void){
_start:
{
lean_object* v___x_5313_; lean_object* v___x_5314_; 
v___x_5313_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16));
v___x_5314_ = l_String_toRawSubstring_x27(v___x_5313_);
return v___x_5314_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24(void){
_start:
{
lean_object* v___x_5327_; lean_object* v___x_5328_; 
v___x_5327_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18));
v___x_5328_ = l_String_toRawSubstring_x27(v___x_5327_);
return v___x_5328_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31(void){
_start:
{
lean_object* v___x_5343_; lean_object* v___x_5344_; 
v___x_5343_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30));
v___x_5344_ = l_String_toRawSubstring_x27(v___x_5343_);
return v___x_5344_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object* v_x_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_){
_start:
{
lean_object* v___x_5372_; uint8_t v___x_5373_; 
v___x_5372_ = ((lean_object*)(l_termPrintln_x21_____00__closed__1));
lean_inc(v_x_5369_);
v___x_5373_ = l_Lean_Syntax_isOfKind(v_x_5369_, v___x_5372_);
if (v___x_5373_ == 0)
{
lean_object* v___x_5374_; lean_object* v___x_5375_; 
lean_dec(v_x_5369_);
v___x_5374_ = lean_box(1);
v___x_5375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5375_, 0, v___x_5374_);
lean_ctor_set(v___x_5375_, 1, v_a_5371_);
return v___x_5375_;
}
else
{
lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; uint8_t v___x_5379_; 
v___x_5376_ = lean_unsigned_to_nat(1u);
v___x_5377_ = l_Lean_Syntax_getArg(v_x_5369_, v___x_5376_);
lean_dec(v_x_5369_);
v___x_5378_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1));
lean_inc(v___x_5377_);
v___x_5379_ = l_Lean_Syntax_isOfKind(v___x_5377_, v___x_5378_);
if (v___x_5379_ == 0)
{
lean_object* v_quotContext_5380_; lean_object* v_currMacroScope_5381_; lean_object* v_ref_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; 
v_quotContext_5380_ = lean_ctor_get(v_a_5370_, 1);
v_currMacroScope_5381_ = lean_ctor_get(v_a_5370_, 2);
v_ref_5382_ = lean_ctor_get(v_a_5370_, 5);
v___x_5383_ = l_Lean_SourceInfo_fromRef(v_ref_5382_, v___x_5379_);
v___x_5384_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3));
v___x_5385_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5));
v___x_5386_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6));
lean_inc_n(v___x_5383_, 14);
v___x_5387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5387_, 0, v___x_5383_);
lean_ctor_set(v___x_5387_, 1, v___x_5386_);
v___x_5388_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8));
v___x_5389_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
v___x_5390_ = lean_box(0);
lean_inc_n(v_currMacroScope_5381_, 4);
lean_inc_n(v_quotContext_5380_, 4);
v___x_5391_ = l_Lean_addMacroScope(v_quotContext_5380_, v___x_5390_, v_currMacroScope_5381_);
v___x_5392_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15));
v___x_5393_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5393_, 0, v___x_5383_);
lean_ctor_set(v___x_5393_, 1, v___x_5389_);
lean_ctor_set(v___x_5393_, 2, v___x_5391_);
lean_ctor_set(v___x_5393_, 3, v___x_5392_);
v___x_5394_ = l_Lean_Syntax_node1(v___x_5383_, v___x_5388_, v___x_5393_);
v___x_5395_ = l_Lean_Syntax_node2(v___x_5383_, v___x_5385_, v___x_5387_, v___x_5394_);
v___x_5396_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_5397_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
v___x_5398_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20));
v___x_5399_ = l_Lean_addMacroScope(v_quotContext_5380_, v___x_5398_, v_currMacroScope_5381_);
v___x_5400_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22));
v___x_5401_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5401_, 0, v___x_5383_);
lean_ctor_set(v___x_5401_, 1, v___x_5397_);
lean_ctor_set(v___x_5401_, 2, v___x_5399_);
lean_ctor_set(v___x_5401_, 3, v___x_5400_);
v___x_5402_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_5403_ = l_Lean_Syntax_node1(v___x_5383_, v___x_5402_, v___x_5377_);
v___x_5404_ = l_Lean_Syntax_node2(v___x_5383_, v___x_5396_, v___x_5401_, v___x_5403_);
v___x_5405_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23));
v___x_5406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5406_, 0, v___x_5383_);
lean_ctor_set(v___x_5406_, 1, v___x_5405_);
v___x_5407_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
v___x_5408_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25));
v___x_5409_ = l_Lean_addMacroScope(v_quotContext_5380_, v___x_5408_, v_currMacroScope_5381_);
v___x_5410_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29));
v___x_5411_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5411_, 0, v___x_5383_);
lean_ctor_set(v___x_5411_, 1, v___x_5407_);
lean_ctor_set(v___x_5411_, 2, v___x_5409_);
lean_ctor_set(v___x_5411_, 3, v___x_5410_);
v___x_5412_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
v___x_5413_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32));
v___x_5414_ = l_Lean_addMacroScope(v_quotContext_5380_, v___x_5413_, v_currMacroScope_5381_);
v___x_5415_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36));
v___x_5416_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5416_, 0, v___x_5383_);
lean_ctor_set(v___x_5416_, 1, v___x_5412_);
lean_ctor_set(v___x_5416_, 2, v___x_5414_);
lean_ctor_set(v___x_5416_, 3, v___x_5415_);
v___x_5417_ = l_Lean_Syntax_node1(v___x_5383_, v___x_5402_, v___x_5416_);
v___x_5418_ = l_Lean_Syntax_node2(v___x_5383_, v___x_5396_, v___x_5411_, v___x_5417_);
v___x_5419_ = l_Lean_Syntax_node1(v___x_5383_, v___x_5402_, v___x_5418_);
v___x_5420_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37));
v___x_5421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5421_, 0, v___x_5383_);
lean_ctor_set(v___x_5421_, 1, v___x_5420_);
v___x_5422_ = l_Lean_Syntax_node5(v___x_5383_, v___x_5384_, v___x_5395_, v___x_5404_, v___x_5406_, v___x_5419_, v___x_5421_);
v___x_5423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5423_, 0, v___x_5422_);
lean_ctor_set(v___x_5423_, 1, v_a_5371_);
return v___x_5423_;
}
else
{
lean_object* v_quotContext_5424_; lean_object* v_currMacroScope_5425_; lean_object* v_ref_5426_; uint8_t v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; 
v_quotContext_5424_ = lean_ctor_get(v_a_5370_, 1);
v_currMacroScope_5425_ = lean_ctor_get(v_a_5370_, 2);
v_ref_5426_ = lean_ctor_get(v_a_5370_, 5);
v___x_5427_ = 0;
v___x_5428_ = l_Lean_SourceInfo_fromRef(v_ref_5426_, v___x_5427_);
v___x_5429_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3));
v___x_5430_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5));
v___x_5431_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6));
lean_inc_n(v___x_5428_, 17);
v___x_5432_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5432_, 0, v___x_5428_);
lean_ctor_set(v___x_5432_, 1, v___x_5431_);
v___x_5433_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8));
v___x_5434_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
v___x_5435_ = lean_box(0);
lean_inc_n(v_currMacroScope_5425_, 4);
lean_inc_n(v_quotContext_5424_, 4);
v___x_5436_ = l_Lean_addMacroScope(v_quotContext_5424_, v___x_5435_, v_currMacroScope_5425_);
v___x_5437_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15));
v___x_5438_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5438_, 0, v___x_5428_);
lean_ctor_set(v___x_5438_, 1, v___x_5434_);
lean_ctor_set(v___x_5438_, 2, v___x_5436_);
lean_ctor_set(v___x_5438_, 3, v___x_5437_);
v___x_5439_ = l_Lean_Syntax_node1(v___x_5428_, v___x_5433_, v___x_5438_);
v___x_5440_ = l_Lean_Syntax_node2(v___x_5428_, v___x_5430_, v___x_5432_, v___x_5439_);
v___x_5441_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_5442_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
v___x_5443_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20));
v___x_5444_ = l_Lean_addMacroScope(v_quotContext_5424_, v___x_5443_, v_currMacroScope_5425_);
v___x_5445_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22));
v___x_5446_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5446_, 0, v___x_5428_);
lean_ctor_set(v___x_5446_, 1, v___x_5442_);
lean_ctor_set(v___x_5446_, 2, v___x_5444_);
lean_ctor_set(v___x_5446_, 3, v___x_5445_);
v___x_5447_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_5448_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39));
v___x_5449_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41));
v___x_5450_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42));
v___x_5451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5451_, 0, v___x_5428_);
lean_ctor_set(v___x_5451_, 1, v___x_5450_);
v___x_5452_ = l_Lean_Syntax_node2(v___x_5428_, v___x_5449_, v___x_5451_, v___x_5377_);
v___x_5453_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37));
v___x_5454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5454_, 0, v___x_5428_);
lean_ctor_set(v___x_5454_, 1, v___x_5453_);
lean_inc_ref(v___x_5454_);
lean_inc(v___x_5440_);
v___x_5455_ = l_Lean_Syntax_node3(v___x_5428_, v___x_5448_, v___x_5440_, v___x_5452_, v___x_5454_);
v___x_5456_ = l_Lean_Syntax_node1(v___x_5428_, v___x_5447_, v___x_5455_);
v___x_5457_ = l_Lean_Syntax_node2(v___x_5428_, v___x_5441_, v___x_5446_, v___x_5456_);
v___x_5458_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23));
v___x_5459_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5459_, 0, v___x_5428_);
lean_ctor_set(v___x_5459_, 1, v___x_5458_);
v___x_5460_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
v___x_5461_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25));
v___x_5462_ = l_Lean_addMacroScope(v_quotContext_5424_, v___x_5461_, v_currMacroScope_5425_);
v___x_5463_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29));
v___x_5464_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5464_, 0, v___x_5428_);
lean_ctor_set(v___x_5464_, 1, v___x_5460_);
lean_ctor_set(v___x_5464_, 2, v___x_5462_);
lean_ctor_set(v___x_5464_, 3, v___x_5463_);
v___x_5465_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
v___x_5466_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32));
v___x_5467_ = l_Lean_addMacroScope(v_quotContext_5424_, v___x_5466_, v_currMacroScope_5425_);
v___x_5468_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36));
v___x_5469_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5469_, 0, v___x_5428_);
lean_ctor_set(v___x_5469_, 1, v___x_5465_);
lean_ctor_set(v___x_5469_, 2, v___x_5467_);
lean_ctor_set(v___x_5469_, 3, v___x_5468_);
v___x_5470_ = l_Lean_Syntax_node1(v___x_5428_, v___x_5447_, v___x_5469_);
v___x_5471_ = l_Lean_Syntax_node2(v___x_5428_, v___x_5441_, v___x_5464_, v___x_5470_);
v___x_5472_ = l_Lean_Syntax_node1(v___x_5428_, v___x_5447_, v___x_5471_);
v___x_5473_ = l_Lean_Syntax_node5(v___x_5428_, v___x_5429_, v___x_5440_, v___x_5457_, v___x_5459_, v___x_5472_, v___x_5454_);
v___x_5474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5474_, 0, v___x_5473_);
lean_ctor_set(v___x_5474_, 1, v_a_5371_);
return v___x_5474_;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___boxed(lean_object* v_x_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_){
_start:
{
lean_object* v_res_5478_; 
v_res_5478_ = l___aux__Init__System__IO______macroRules__termPrintln_x21______1(v_x_5475_, v_a_5476_, v_a_5477_);
lean_dec_ref(v_a_5476_);
return v_res_5478_;
}
}
LEAN_EXPORT lean_object* l_Runtime_markMultiThreaded___boxed(lean_object* v_00_u03b1_5482_, lean_object* v_a_5483_, lean_object* v_a_00___x40___internal___hyg_5484_){
_start:
{
lean_object* v_res_5485_; 
v_res_5485_ = lean_runtime_mark_multi_threaded(v_a_5483_);
return v_res_5485_;
}
}
LEAN_EXPORT lean_object* l_Runtime_markPersistent___boxed(lean_object* v_00_u03b1_5489_, lean_object* v_a_5490_, lean_object* v_a_00___x40___internal___hyg_5491_){
_start:
{
lean_object* v_res_5492_; 
v_res_5492_ = lean_runtime_mark_persistent(v_a_5490_);
return v_res_5492_;
}
}
LEAN_EXPORT lean_object* l_Runtime_forget___boxed(lean_object* v_00_u03b1_5496_, lean_object* v_a_5497_, lean_object* v_a_00___x40___internal___hyg_5498_){
_start:
{
lean_object* v_res_5499_; 
v_res_5499_ = lean_runtime_forget(v_a_5497_);
return v_res_5499_;
}
}
LEAN_EXPORT lean_object* l_Runtime_hold___boxed(lean_object* v_00_u03b1_5503_, lean_object* v_a_5504_, lean_object* v_a_00___x40___internal___hyg_5505_){
_start:
{
lean_object* v_res_5506_; 
v_res_5506_ = lean_runtime_hold(v_a_5504_);
lean_dec(v_a_5504_);
return v_res_5506_;
}
}
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IOError(uint8_t builtin);
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Repr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_IO(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IOError(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_IO_RealWorld_nonemptyType = _init_l_IO_RealWorld_nonemptyType();
l_IO_instInhabitedTaskState_default = _init_l_IO_instInhabitedTaskState_default();
l_IO_instInhabitedTaskState = _init_l_IO_instInhabitedTaskState();
l_IO_instLTTaskState = _init_l_IO_instLTTaskState();
lean_mark_persistent(l_IO_instLTTaskState);
l_IO_instLETaskState = _init_l_IO_instLETaskState();
lean_mark_persistent(l_IO_instLETaskState);
l_IO_FS_instInhabitedSystemTime_default = _init_l_IO_FS_instInhabitedSystemTime_default();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime_default);
l_IO_FS_instInhabitedSystemTime = _init_l_IO_FS_instInhabitedSystemTime();
lean_mark_persistent(l_IO_FS_instInhabitedSystemTime);
l_IO_FS_instLTSystemTime = _init_l_IO_FS_instLTSystemTime();
lean_mark_persistent(l_IO_FS_instLTSystemTime);
l_IO_FS_instLESystemTime = _init_l_IO_FS_instLESystemTime();
lean_mark_persistent(l_IO_FS_instLESystemTime);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_System_IO(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_IO_waitAny___auto__1 = _init_l_IO_waitAny___auto__1();
lean_mark_persistent(l_IO_waitAny___auto__1);
l_IO_waitAny_x27___auto__1 = _init_l_IO_waitAny_x27___auto__1();
lean_mark_persistent(l_IO_waitAny_x27___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Init_System_IOError(uint8_t builtin);
lean_object* initialize_Init_System_FilePath(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Repr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_IO(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IOError(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_System_IO(builtin);
}
#ifdef __cplusplus
}
#endif
