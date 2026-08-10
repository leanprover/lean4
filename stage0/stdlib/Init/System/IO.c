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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
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
static lean_object* l_IO_FS_instInhabitedSystemTime_default___closed__0;
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
lean_dec_ref_known(v___x_319_, 1);
return v_a_320_;
}
else
{
lean_object* v_a_321_; lean_object* v___x_322_; 
v_a_321_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_319_, 1);
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
lean_dec_ref_known(v___x_332_, 1);
return v_a_333_;
}
else
{
lean_object* v_a_334_; lean_object* v___x_335_; 
v_a_334_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_332_, 1);
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
lean_dec_ref_known(v___x_471_, 1);
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
lean_dec_ref_known(v___x_510_, 1);
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
lean_dec_ref_known(v___x_549_, 1);
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
lean_dec_ref_known(v___x_579_, 1);
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
lean_dec_ref_known(v___x_609_, 1);
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
lean_dec_ref_known(v___x_630_, 1);
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
lean_dec_ref_known(v___x_651_, 1);
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
lean_dec_ref_known(v___x_672_, 1);
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
lean_dec_ref_known(v_r_714_, 1);
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
lean_dec_ref_known(v_r_770_, 1);
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
lean_dec_ref_known(v___x_896_, 1);
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
lean_dec_ref_known(v___x_908_, 1);
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
lean_dec_ref_known(v___x_1029_, 1);
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
lean_dec_ref_known(v___x_1041_, 1);
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
lean_dec_ref_known(v_x_1521_, 2);
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
lean_dec_ref_known(v_x_1521_, 2);
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
lean_dec_ref_known(v___x_1688_, 1);
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
lean_dec_ref_known(v___x_2010_, 1);
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
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg(lean_object* v_k_2159_){
_start:
{
lean_inc(v_k_2159_);
return v_k_2159_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg___boxed(lean_object* v_k_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_IO_TaskState_ctorElim___redArg(v_k_2160_);
lean_dec(v_k_2160_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim(lean_object* v_motive_2162_, lean_object* v_ctorIdx_2163_, uint8_t v_t_2164_, lean_object* v_h_2165_, lean_object* v_k_2166_){
_start:
{
lean_inc(v_k_2166_);
return v_k_2166_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___boxed(lean_object* v_motive_2167_, lean_object* v_ctorIdx_2168_, lean_object* v_t_2169_, lean_object* v_h_2170_, lean_object* v_k_2171_){
_start:
{
uint8_t v_t_boxed_2172_; lean_object* v_res_2173_; 
v_t_boxed_2172_ = lean_unbox(v_t_2169_);
v_res_2173_ = l_IO_TaskState_ctorElim(v_motive_2167_, v_ctorIdx_2168_, v_t_boxed_2172_, v_h_2170_, v_k_2171_);
lean_dec(v_k_2171_);
lean_dec(v_ctorIdx_2168_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg(lean_object* v_waiting_2174_){
_start:
{
lean_inc(v_waiting_2174_);
return v_waiting_2174_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg___boxed(lean_object* v_waiting_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_IO_TaskState_waiting_elim___redArg(v_waiting_2175_);
lean_dec(v_waiting_2175_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim(lean_object* v_motive_2177_, uint8_t v_t_2178_, lean_object* v_h_2179_, lean_object* v_waiting_2180_){
_start:
{
lean_inc(v_waiting_2180_);
return v_waiting_2180_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___boxed(lean_object* v_motive_2181_, lean_object* v_t_2182_, lean_object* v_h_2183_, lean_object* v_waiting_2184_){
_start:
{
uint8_t v_t_boxed_2185_; lean_object* v_res_2186_; 
v_t_boxed_2185_ = lean_unbox(v_t_2182_);
v_res_2186_ = l_IO_TaskState_waiting_elim(v_motive_2181_, v_t_boxed_2185_, v_h_2183_, v_waiting_2184_);
lean_dec(v_waiting_2184_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg(lean_object* v_running_2187_){
_start:
{
lean_inc(v_running_2187_);
return v_running_2187_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg___boxed(lean_object* v_running_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_IO_TaskState_running_elim___redArg(v_running_2188_);
lean_dec(v_running_2188_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim(lean_object* v_motive_2190_, uint8_t v_t_2191_, lean_object* v_h_2192_, lean_object* v_running_2193_){
_start:
{
lean_inc(v_running_2193_);
return v_running_2193_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___boxed(lean_object* v_motive_2194_, lean_object* v_t_2195_, lean_object* v_h_2196_, lean_object* v_running_2197_){
_start:
{
uint8_t v_t_boxed_2198_; lean_object* v_res_2199_; 
v_t_boxed_2198_ = lean_unbox(v_t_2195_);
v_res_2199_ = l_IO_TaskState_running_elim(v_motive_2194_, v_t_boxed_2198_, v_h_2196_, v_running_2197_);
lean_dec(v_running_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg(lean_object* v_finished_2200_){
_start:
{
lean_inc(v_finished_2200_);
return v_finished_2200_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg___boxed(lean_object* v_finished_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_IO_TaskState_finished_elim___redArg(v_finished_2201_);
lean_dec(v_finished_2201_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim(lean_object* v_motive_2203_, uint8_t v_t_2204_, lean_object* v_h_2205_, lean_object* v_finished_2206_){
_start:
{
lean_inc(v_finished_2206_);
return v_finished_2206_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___boxed(lean_object* v_motive_2207_, lean_object* v_t_2208_, lean_object* v_h_2209_, lean_object* v_finished_2210_){
_start:
{
uint8_t v_t_boxed_2211_; lean_object* v_res_2212_; 
v_t_boxed_2211_ = lean_unbox(v_t_2208_);
v_res_2212_ = l_IO_TaskState_finished_elim(v_motive_2207_, v_t_boxed_2211_, v_h_2209_, v_finished_2210_);
lean_dec(v_finished_2210_);
return v_res_2212_;
}
}
static uint8_t _init_l_IO_instInhabitedTaskState_default(void){
_start:
{
uint8_t v___x_2213_; 
v___x_2213_ = 0;
return v___x_2213_;
}
}
static uint8_t _init_l_IO_instInhabitedTaskState(void){
_start:
{
uint8_t v___x_2214_; 
v___x_2214_ = 0;
return v___x_2214_;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__6(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = lean_unsigned_to_nat(2u);
v___x_2225_ = lean_nat_to_int(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__7(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_unsigned_to_nat(1u);
v___x_2227_ = lean_nat_to_int(v___x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr(uint8_t v_x_2228_, lean_object* v_prec_2229_){
_start:
{
lean_object* v___y_2231_; lean_object* v___y_2238_; lean_object* v___y_2245_; 
switch(v_x_2228_)
{
case 0:
{
lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = lean_unsigned_to_nat(1024u);
v___x_2252_ = lean_nat_dec_le(v___x_2251_, v_prec_2229_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2231_ = v___x_2253_;
goto v___jp_2230_;
}
else
{
lean_object* v___x_2254_; 
v___x_2254_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2231_ = v___x_2254_;
goto v___jp_2230_;
}
}
case 1:
{
lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = lean_unsigned_to_nat(1024u);
v___x_2256_ = lean_nat_dec_le(v___x_2255_, v_prec_2229_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2238_ = v___x_2257_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2238_ = v___x_2258_;
goto v___jp_2237_;
}
}
default: 
{
lean_object* v___x_2259_; uint8_t v___x_2260_; 
v___x_2259_ = lean_unsigned_to_nat(1024u);
v___x_2260_ = lean_nat_dec_le(v___x_2259_, v_prec_2229_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; 
v___x_2261_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2245_ = v___x_2261_;
goto v___jp_2244_;
}
else
{
lean_object* v___x_2262_; 
v___x_2262_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2245_ = v___x_2262_;
goto v___jp_2244_;
}
}
}
v___jp_2230_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2232_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__1));
lean_inc(v___y_2231_);
v___x_2233_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___y_2231_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = 0;
v___x_2235_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2235_, 0, v___x_2233_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*1, v___x_2234_);
v___x_2236_ = l_Repr_addAppParen(v___x_2235_, v_prec_2229_);
return v___x_2236_;
}
v___jp_2237_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2239_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__3));
lean_inc(v___y_2238_);
v___x_2240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___y_2238_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = 0;
v___x_2242_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*1, v___x_2241_);
v___x_2243_ = l_Repr_addAppParen(v___x_2242_, v_prec_2229_);
return v___x_2243_;
}
v___jp_2244_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2246_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__5));
lean_inc(v___y_2245_);
v___x_2247_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___y_2245_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
v___x_2248_ = 0;
v___x_2249_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2249_, 0, v___x_2247_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*1, v___x_2248_);
v___x_2250_ = l_Repr_addAppParen(v___x_2249_, v_prec_2229_);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr___boxed(lean_object* v_x_2263_, lean_object* v_prec_2264_){
_start:
{
uint8_t v_x_177__boxed_2265_; lean_object* v_res_2266_; 
v_x_177__boxed_2265_ = lean_unbox(v_x_2263_);
v_res_2266_ = l_IO_instReprTaskState_repr(v_x_177__boxed_2265_, v_prec_2264_);
lean_dec(v_prec_2264_);
return v_res_2266_;
}
}
LEAN_EXPORT uint8_t l_IO_TaskState_ofNat(lean_object* v_n_2269_){
_start:
{
lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = lean_nat_dec_le(v_n_2269_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = lean_nat_dec_le(v_n_2269_, v___x_2272_);
if (v___x_2273_ == 0)
{
uint8_t v___x_2274_; 
v___x_2274_ = 2;
return v___x_2274_;
}
else
{
uint8_t v___x_2275_; 
v___x_2275_ = 1;
return v___x_2275_;
}
}
else
{
uint8_t v___x_2276_; 
v___x_2276_ = 0;
return v___x_2276_;
}
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ofNat___boxed(lean_object* v_n_2277_){
_start:
{
uint8_t v_res_2278_; lean_object* v_r_2279_; 
v_res_2278_ = l_IO_TaskState_ofNat(v_n_2277_);
lean_dec(v_n_2277_);
v_r_2279_ = lean_box(v_res_2278_);
return v_r_2279_;
}
}
LEAN_EXPORT uint8_t l_IO_instDecidableEqTaskState(uint8_t v_x_2280_, uint8_t v_y_2281_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2282_ = l_IO_TaskState_ctorIdx(v_x_2280_);
v___x_2283_ = l_IO_TaskState_ctorIdx(v_y_2281_);
v___x_2284_ = lean_nat_dec_eq(v___x_2282_, v___x_2283_);
lean_dec(v___x_2283_);
lean_dec(v___x_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_IO_instDecidableEqTaskState___boxed(lean_object* v_x_2285_, lean_object* v_y_2286_){
_start:
{
uint8_t v_x_13__boxed_2287_; uint8_t v_y_14__boxed_2288_; uint8_t v_res_2289_; lean_object* v_r_2290_; 
v_x_13__boxed_2287_ = lean_unbox(v_x_2285_);
v_y_14__boxed_2288_ = lean_unbox(v_y_2286_);
v_res_2289_ = l_IO_instDecidableEqTaskState(v_x_13__boxed_2287_, v_y_14__boxed_2288_);
v_r_2290_ = lean_box(v_res_2289_);
return v_r_2290_;
}
}
LEAN_EXPORT uint8_t l_IO_instOrdTaskState_ord(uint8_t v_x_2291_, uint8_t v_y_2292_){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2293_ = l_IO_TaskState_ctorIdx(v_x_2291_);
v___x_2294_ = l_IO_TaskState_ctorIdx(v_y_2292_);
v___x_2295_ = lean_nat_dec_lt(v___x_2293_, v___x_2294_);
if (v___x_2295_ == 0)
{
uint8_t v___x_2296_; 
v___x_2296_ = lean_nat_dec_eq(v___x_2293_, v___x_2294_);
lean_dec(v___x_2294_);
lean_dec(v___x_2293_);
if (v___x_2296_ == 0)
{
uint8_t v___x_2297_; 
v___x_2297_ = 2;
return v___x_2297_;
}
else
{
uint8_t v___x_2298_; 
v___x_2298_ = 1;
return v___x_2298_;
}
}
else
{
uint8_t v___x_2299_; 
lean_dec(v___x_2294_);
lean_dec(v___x_2293_);
v___x_2299_ = 0;
return v___x_2299_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instOrdTaskState_ord___boxed(lean_object* v_x_2300_, lean_object* v_y_2301_){
_start:
{
uint8_t v_x_30__boxed_2302_; uint8_t v_y_31__boxed_2303_; uint8_t v_res_2304_; lean_object* v_r_2305_; 
v_x_30__boxed_2302_ = lean_unbox(v_x_2300_);
v_y_31__boxed_2303_ = lean_unbox(v_y_2301_);
v_res_2304_ = l_IO_instOrdTaskState_ord(v_x_30__boxed_2302_, v_y_31__boxed_2303_);
v_r_2305_ = lean_box(v_res_2304_);
return v_r_2305_;
}
}
static lean_object* _init_l_IO_instLTTaskState(void){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_box(0);
return v___x_2308_;
}
}
static lean_object* _init_l_IO_instLETaskState(void){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = lean_box(0);
return v___x_2309_;
}
}
LEAN_EXPORT uint8_t l_IO_instMinTaskState___lam__0(uint8_t v_x_2310_, uint8_t v_y_2311_){
_start:
{
uint8_t v___x_2312_; 
v___x_2312_ = l_IO_instOrdTaskState_ord(v_x_2310_, v_y_2311_);
if (v___x_2312_ == 2)
{
return v_y_2311_;
}
else
{
return v_x_2310_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instMinTaskState___lam__0___boxed(lean_object* v_x_2313_, lean_object* v_y_2314_){
_start:
{
uint8_t v_x_boxed_2315_; uint8_t v_y_boxed_2316_; uint8_t v_res_2317_; lean_object* v_r_2318_; 
v_x_boxed_2315_ = lean_unbox(v_x_2313_);
v_y_boxed_2316_ = lean_unbox(v_y_2314_);
v_res_2317_ = l_IO_instMinTaskState___lam__0(v_x_boxed_2315_, v_y_boxed_2316_);
v_r_2318_ = lean_box(v_res_2317_);
return v_r_2318_;
}
}
LEAN_EXPORT uint8_t l_IO_instMaxTaskState___lam__0(uint8_t v_x_2321_, uint8_t v_y_2322_){
_start:
{
uint8_t v___x_2323_; 
v___x_2323_ = l_IO_instOrdTaskState_ord(v_x_2321_, v_y_2322_);
if (v___x_2323_ == 2)
{
return v_x_2321_;
}
else
{
return v_y_2322_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instMaxTaskState___lam__0___boxed(lean_object* v_x_2324_, lean_object* v_y_2325_){
_start:
{
uint8_t v_x_boxed_2326_; uint8_t v_y_boxed_2327_; uint8_t v_res_2328_; lean_object* v_r_2329_; 
v_x_boxed_2326_ = lean_unbox(v_x_2324_);
v_y_boxed_2327_ = lean_unbox(v_y_2325_);
v_res_2328_ = l_IO_instMaxTaskState___lam__0(v_x_boxed_2326_, v_y_boxed_2327_);
v_r_2329_ = lean_box(v_res_2328_);
return v_r_2329_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toString(uint8_t v_x_2335_){
_start:
{
switch(v_x_2335_)
{
case 0:
{
lean_object* v___x_2336_; 
v___x_2336_ = ((lean_object*)(l_IO_TaskState_toString___closed__0));
return v___x_2336_;
}
case 1:
{
lean_object* v___x_2337_; 
v___x_2337_ = ((lean_object*)(l_IO_TaskState_toString___closed__1));
return v___x_2337_;
}
default: 
{
lean_object* v___x_2338_; 
v___x_2338_ = ((lean_object*)(l_IO_TaskState_toString___closed__2));
return v___x_2338_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toString___boxed(lean_object* v_x_2339_){
_start:
{
uint8_t v_x_31__boxed_2340_; lean_object* v_res_2341_; 
v_x_31__boxed_2340_ = lean_unbox(v_x_2339_);
v_res_2341_ = l_IO_TaskState_toString(v_x_31__boxed_2340_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_IO_getTaskState___boxed(lean_object* v_00_u03b1_2347_, lean_object* v_a_00___x40___internal___hyg_2348_, lean_object* v_a_00___x40___internal___hyg_2349_){
_start:
{
uint8_t v_res_2350_; lean_object* v_r_2351_; 
v_res_2350_ = lean_io_get_task_state(v_a_00___x40___internal___hyg_2348_);
lean_dec_ref(v_a_00___x40___internal___hyg_2348_);
v_r_2351_ = lean_box(v_res_2350_);
return v_r_2351_;
}
}
LEAN_EXPORT uint8_t l_IO_hasFinished___redArg(lean_object* v_task_2352_){
_start:
{
uint8_t v___x_2354_; 
v___x_2354_ = lean_io_get_task_state(v_task_2352_);
if (v___x_2354_ == 2)
{
uint8_t v___x_2355_; 
v___x_2355_ = 1;
return v___x_2355_;
}
else
{
uint8_t v___x_2356_; 
v___x_2356_ = 0;
return v___x_2356_;
}
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___redArg___boxed(lean_object* v_task_2357_, lean_object* v_a_2358_){
_start:
{
uint8_t v_res_2359_; lean_object* v_r_2360_; 
v_res_2359_ = l_IO_hasFinished___redArg(v_task_2357_);
lean_dec_ref(v_task_2357_);
v_r_2360_ = lean_box(v_res_2359_);
return v_r_2360_;
}
}
LEAN_EXPORT uint8_t l_IO_hasFinished(lean_object* v_00_u03b1_2361_, lean_object* v_task_2362_){
_start:
{
uint8_t v___x_2364_; 
v___x_2364_ = lean_io_get_task_state(v_task_2362_);
if (v___x_2364_ == 2)
{
uint8_t v___x_2365_; 
v___x_2365_ = 1;
return v___x_2365_;
}
else
{
uint8_t v___x_2366_; 
v___x_2366_ = 0;
return v___x_2366_;
}
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object* v_00_u03b1_2367_, lean_object* v_task_2368_, lean_object* v_a_2369_){
_start:
{
uint8_t v_res_2370_; lean_object* v_r_2371_; 
v_res_2370_ = l_IO_hasFinished(v_00_u03b1_2367_, v_task_2368_);
lean_dec_ref(v_task_2368_);
v_r_2371_ = lean_box(v_res_2370_);
return v_r_2371_;
}
}
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object* v_00_u03b1_2375_, lean_object* v_t_2376_, lean_object* v_a_00___x40___internal___hyg_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = lean_io_wait(v_t_2376_);
return v_res_2378_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__10));
v___x_2406_ = l_Lean_mkAtom(v___x_2405_);
return v___x_2406_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__12, &l_IO_waitAny___auto__1___closed__12_once, _init_l_IO_waitAny___auto__1___closed__12);
v___x_2408_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2409_ = lean_array_push(v___x_2408_, v___x_2407_);
return v___x_2409_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__17));
v___x_2419_ = lean_string_utf8_byte_size(v___x_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2420_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__18, &l_IO_waitAny___auto__1___closed__18_once, _init_l_IO_waitAny___auto__1___closed__18);
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__17));
v___x_2423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
lean_ctor_set(v___x_2423_, 1, v___x_2421_);
lean_ctor_set(v___x_2423_, 2, v___x_2420_);
return v___x_2423_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2429_ = lean_box(0);
v___x_2430_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__22));
v___x_2431_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__19, &l_IO_waitAny___auto__1___closed__19_once, _init_l_IO_waitAny___auto__1___closed__19);
v___x_2432_ = lean_box(2);
v___x_2433_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
lean_ctor_set(v___x_2433_, 1, v___x_2431_);
lean_ctor_set(v___x_2433_, 2, v___x_2430_);
lean_ctor_set(v___x_2433_, 3, v___x_2429_);
return v___x_2433_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__23, &l_IO_waitAny___auto__1___closed__23_once, _init_l_IO_waitAny___auto__1___closed__23);
v___x_2435_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2436_ = lean_array_push(v___x_2435_, v___x_2434_);
return v___x_2436_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__28(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__27));
v___x_2445_ = l_Lean_mkAtom(v___x_2444_);
return v___x_2445_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__29(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__28, &l_IO_waitAny___auto__1___closed__28_once, _init_l_IO_waitAny___auto__1___closed__28);
v___x_2447_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2448_ = lean_array_push(v___x_2447_, v___x_2446_);
return v___x_2448_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__30(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2449_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__29, &l_IO_waitAny___auto__1___closed__29_once, _init_l_IO_waitAny___auto__1___closed__29);
v___x_2450_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__26));
v___x_2451_ = lean_box(2);
v___x_2452_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
lean_ctor_set(v___x_2452_, 1, v___x_2450_);
lean_ctor_set(v___x_2452_, 2, v___x_2449_);
return v___x_2452_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__31(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__30, &l_IO_waitAny___auto__1___closed__30_once, _init_l_IO_waitAny___auto__1___closed__30);
v___x_2454_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2455_ = lean_array_push(v___x_2454_, v___x_2453_);
return v___x_2455_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__32(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2456_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__31, &l_IO_waitAny___auto__1___closed__31_once, _init_l_IO_waitAny___auto__1___closed__31);
v___x_2457_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_2458_ = lean_box(2);
v___x_2459_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
lean_ctor_set(v___x_2459_, 1, v___x_2457_);
lean_ctor_set(v___x_2459_, 2, v___x_2456_);
return v___x_2459_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__33(void){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__32, &l_IO_waitAny___auto__1___closed__32_once, _init_l_IO_waitAny___auto__1___closed__32);
v___x_2461_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__24, &l_IO_waitAny___auto__1___closed__24_once, _init_l_IO_waitAny___auto__1___closed__24);
v___x_2462_ = lean_array_push(v___x_2461_, v___x_2460_);
return v___x_2462_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__34(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2463_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__33, &l_IO_waitAny___auto__1___closed__33_once, _init_l_IO_waitAny___auto__1___closed__33);
v___x_2464_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_2465_ = lean_box(2);
v___x_2466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
lean_ctor_set(v___x_2466_, 1, v___x_2464_);
lean_ctor_set(v___x_2466_, 2, v___x_2463_);
return v___x_2466_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__35(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__34, &l_IO_waitAny___auto__1___closed__34_once, _init_l_IO_waitAny___auto__1___closed__34);
v___x_2468_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__13, &l_IO_waitAny___auto__1___closed__13_once, _init_l_IO_waitAny___auto__1___closed__13);
v___x_2469_ = lean_array_push(v___x_2468_, v___x_2467_);
return v___x_2469_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__36(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2470_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__35, &l_IO_waitAny___auto__1___closed__35_once, _init_l_IO_waitAny___auto__1___closed__35);
v___x_2471_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__11));
v___x_2472_ = lean_box(2);
v___x_2473_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v___x_2471_);
lean_ctor_set(v___x_2473_, 2, v___x_2470_);
return v___x_2473_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__37(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__36, &l_IO_waitAny___auto__1___closed__36_once, _init_l_IO_waitAny___auto__1___closed__36);
v___x_2475_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2476_ = lean_array_push(v___x_2475_, v___x_2474_);
return v___x_2476_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__38(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2477_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__37, &l_IO_waitAny___auto__1___closed__37_once, _init_l_IO_waitAny___auto__1___closed__37);
v___x_2478_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_2479_ = lean_box(2);
v___x_2480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v___x_2478_);
lean_ctor_set(v___x_2480_, 2, v___x_2477_);
return v___x_2480_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__39(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__38, &l_IO_waitAny___auto__1___closed__38_once, _init_l_IO_waitAny___auto__1___closed__38);
v___x_2482_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2483_ = lean_array_push(v___x_2482_, v___x_2481_);
return v___x_2483_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__40(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2484_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__39, &l_IO_waitAny___auto__1___closed__39_once, _init_l_IO_waitAny___auto__1___closed__39);
v___x_2485_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__7));
v___x_2486_ = lean_box(2);
v___x_2487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
lean_ctor_set(v___x_2487_, 1, v___x_2485_);
lean_ctor_set(v___x_2487_, 2, v___x_2484_);
return v___x_2487_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__41(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__40, &l_IO_waitAny___auto__1___closed__40_once, _init_l_IO_waitAny___auto__1___closed__40);
v___x_2489_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2490_ = lean_array_push(v___x_2489_, v___x_2488_);
return v___x_2490_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__42(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2491_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__41, &l_IO_waitAny___auto__1___closed__41_once, _init_l_IO_waitAny___auto__1___closed__41);
v___x_2492_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__4));
v___x_2493_ = lean_box(2);
v___x_2494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
lean_ctor_set(v___x_2494_, 1, v___x_2492_);
lean_ctor_set(v___x_2494_, 2, v___x_2491_);
return v___x_2494_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1(void){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__42, &l_IO_waitAny___auto__1___closed__42_once, _init_l_IO_waitAny___auto__1___closed__42);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object* v_00_u03b1_2500_, lean_object* v_tasks_2501_, lean_object* v_h_2502_, lean_object* v_a_00___x40___internal___hyg_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = lean_io_wait_any(v_tasks_2501_);
lean_dec(v_tasks_2501_);
return v_res_2504_;
}
}
static lean_object* _init_l_IO_waitAny_x27___auto__1(void){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__42, &l_IO_waitAny___auto__1___closed__42_once, _init_l_IO_waitAny___auto__1___closed__42);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0(lean_object* v___x_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2506_);
lean_ctor_set(v___x_2508_, 1, v_a_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
if (lean_obj_tag(v_a_2509_) == 0)
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_array_to_list(v_a_2510_);
return v___x_2511_;
}
else
{
lean_object* v_head_2512_; lean_object* v_tail_2513_; lean_object* v___x_2514_; lean_object* v___f_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v_head_2512_ = lean_ctor_get(v_a_2509_, 0);
lean_inc(v_head_2512_);
v_tail_2513_ = lean_ctor_get(v_a_2509_, 1);
lean_inc(v_tail_2513_);
lean_dec_ref_known(v_a_2509_, 2);
v___x_2514_ = lean_array_get_size(v_a_2510_);
v___f_2515_ = lean_alloc_closure((void*)(l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2515_, 0, v___x_2514_);
v___x_2516_ = lean_unsigned_to_nat(0u);
v___x_2517_ = 1;
v___x_2518_ = lean_task_map(v___f_2515_, v_head_2512_, v___x_2516_, v___x_2517_);
v___x_2519_ = lean_array_push(v_a_2510_, v___x_2518_);
v_a_2509_ = v_tail_2513_;
v_a_2510_ = v___x_2519_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg(lean_object* v_tasks_2523_){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v_fst_2528_; lean_object* v_snd_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2537_; 
v___x_2525_ = ((lean_object*)(l_IO_waitAny_x27___redArg___closed__0));
lean_inc(v_tasks_2523_);
v___x_2526_ = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(v_tasks_2523_, v___x_2525_);
v___x_2527_ = lean_io_wait_any(v___x_2526_);
lean_dec(v___x_2526_);
v_fst_2528_ = lean_ctor_get(v___x_2527_, 0);
v_snd_2529_ = lean_ctor_get(v___x_2527_, 1);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2531_ = v___x_2527_;
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_snd_2529_);
lean_inc(v_fst_2528_);
lean_dec(v___x_2527_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2533_; lean_object* v___x_2535_; 
lean_inc(v_tasks_2523_);
v___x_2533_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_box(0), v_tasks_2523_, v_tasks_2523_, v_fst_2528_, v___x_2525_);
lean_dec(v_tasks_2523_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 1, v___x_2533_);
lean_ctor_set(v___x_2531_, 0, v_snd_2529_);
v___x_2535_ = v___x_2531_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_snd_2529_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg___boxed(lean_object* v_tasks_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_IO_waitAny_x27___redArg(v_tasks_2538_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27(lean_object* v_00_u03b1_2541_, lean_object* v_tasks_2542_, lean_object* v_h_2543_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_IO_waitAny_x27___redArg(v_tasks_2542_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___boxed(lean_object* v_00_u03b1_2546_, lean_object* v_tasks_2547_, lean_object* v_h_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_IO_waitAny_x27(v_00_u03b1_2546_, v_tasks_2547_, v_h_2548_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0(lean_object* v_00_u03b1_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(v_a_2552_, v_a_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object* v_a_00___x40___internal___hyg_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = lean_io_get_num_heartbeats();
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_IO_setNumHeartbeats___boxed(lean_object* v_count_2560_, lean_object* v_a_00___x40___internal___hyg_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = lean_io_set_heartbeats(v_count_2560_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_IO_addHeartbeats(lean_object* v_count_2563_){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2565_ = lean_io_get_num_heartbeats();
v___x_2566_ = lean_nat_add(v___x_2565_, v_count_2563_);
lean_dec(v___x_2565_);
v___x_2567_ = lean_io_set_heartbeats(v___x_2566_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_IO_addHeartbeats___boxed(lean_object* v_count_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_IO_addHeartbeats(v_count_2568_);
lean_dec(v_count_2568_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx(uint8_t v_x_2571_){
_start:
{
switch(v_x_2571_)
{
case 0:
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_unsigned_to_nat(0u);
return v___x_2572_;
}
case 1:
{
lean_object* v___x_2573_; 
v___x_2573_ = lean_unsigned_to_nat(1u);
return v___x_2573_;
}
case 2:
{
lean_object* v___x_2574_; 
v___x_2574_ = lean_unsigned_to_nat(2u);
return v___x_2574_;
}
case 3:
{
lean_object* v___x_2575_; 
v___x_2575_ = lean_unsigned_to_nat(3u);
return v___x_2575_;
}
default: 
{
lean_object* v___x_2576_; 
v___x_2576_ = lean_unsigned_to_nat(4u);
return v___x_2576_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx___boxed(lean_object* v_x_2577_){
_start:
{
uint8_t v_x_boxed_2578_; lean_object* v_res_2579_; 
v_x_boxed_2578_ = lean_unbox(v_x_2577_);
v_res_2579_ = l_IO_FS_Mode_ctorIdx(v_x_boxed_2578_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg(lean_object* v_k_2580_){
_start:
{
lean_inc(v_k_2580_);
return v_k_2580_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg___boxed(lean_object* v_k_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_IO_FS_Mode_ctorElim___redArg(v_k_2581_);
lean_dec(v_k_2581_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim(lean_object* v_motive_2583_, lean_object* v_ctorIdx_2584_, uint8_t v_t_2585_, lean_object* v_h_2586_, lean_object* v_k_2587_){
_start:
{
lean_inc(v_k_2587_);
return v_k_2587_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___boxed(lean_object* v_motive_2588_, lean_object* v_ctorIdx_2589_, lean_object* v_t_2590_, lean_object* v_h_2591_, lean_object* v_k_2592_){
_start:
{
uint8_t v_t_boxed_2593_; lean_object* v_res_2594_; 
v_t_boxed_2593_ = lean_unbox(v_t_2590_);
v_res_2594_ = l_IO_FS_Mode_ctorElim(v_motive_2588_, v_ctorIdx_2589_, v_t_boxed_2593_, v_h_2591_, v_k_2592_);
lean_dec(v_k_2592_);
lean_dec(v_ctorIdx_2589_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg(lean_object* v_read_2595_){
_start:
{
lean_inc(v_read_2595_);
return v_read_2595_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg___boxed(lean_object* v_read_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_IO_FS_Mode_read_elim___redArg(v_read_2596_);
lean_dec(v_read_2596_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim(lean_object* v_motive_2598_, uint8_t v_t_2599_, lean_object* v_h_2600_, lean_object* v_read_2601_){
_start:
{
lean_inc(v_read_2601_);
return v_read_2601_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___boxed(lean_object* v_motive_2602_, lean_object* v_t_2603_, lean_object* v_h_2604_, lean_object* v_read_2605_){
_start:
{
uint8_t v_t_boxed_2606_; lean_object* v_res_2607_; 
v_t_boxed_2606_ = lean_unbox(v_t_2603_);
v_res_2607_ = l_IO_FS_Mode_read_elim(v_motive_2602_, v_t_boxed_2606_, v_h_2604_, v_read_2605_);
lean_dec(v_read_2605_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg(lean_object* v_write_2608_){
_start:
{
lean_inc(v_write_2608_);
return v_write_2608_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg___boxed(lean_object* v_write_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_IO_FS_Mode_write_elim___redArg(v_write_2609_);
lean_dec(v_write_2609_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim(lean_object* v_motive_2611_, uint8_t v_t_2612_, lean_object* v_h_2613_, lean_object* v_write_2614_){
_start:
{
lean_inc(v_write_2614_);
return v_write_2614_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___boxed(lean_object* v_motive_2615_, lean_object* v_t_2616_, lean_object* v_h_2617_, lean_object* v_write_2618_){
_start:
{
uint8_t v_t_boxed_2619_; lean_object* v_res_2620_; 
v_t_boxed_2619_ = lean_unbox(v_t_2616_);
v_res_2620_ = l_IO_FS_Mode_write_elim(v_motive_2615_, v_t_boxed_2619_, v_h_2617_, v_write_2618_);
lean_dec(v_write_2618_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg(lean_object* v_writeNew_2621_){
_start:
{
lean_inc(v_writeNew_2621_);
return v_writeNew_2621_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg___boxed(lean_object* v_writeNew_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_IO_FS_Mode_writeNew_elim___redArg(v_writeNew_2622_);
lean_dec(v_writeNew_2622_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim(lean_object* v_motive_2624_, uint8_t v_t_2625_, lean_object* v_h_2626_, lean_object* v_writeNew_2627_){
_start:
{
lean_inc(v_writeNew_2627_);
return v_writeNew_2627_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___boxed(lean_object* v_motive_2628_, lean_object* v_t_2629_, lean_object* v_h_2630_, lean_object* v_writeNew_2631_){
_start:
{
uint8_t v_t_boxed_2632_; lean_object* v_res_2633_; 
v_t_boxed_2632_ = lean_unbox(v_t_2629_);
v_res_2633_ = l_IO_FS_Mode_writeNew_elim(v_motive_2628_, v_t_boxed_2632_, v_h_2630_, v_writeNew_2631_);
lean_dec(v_writeNew_2631_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg(lean_object* v_readWrite_2634_){
_start:
{
lean_inc(v_readWrite_2634_);
return v_readWrite_2634_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg___boxed(lean_object* v_readWrite_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_IO_FS_Mode_readWrite_elim___redArg(v_readWrite_2635_);
lean_dec(v_readWrite_2635_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim(lean_object* v_motive_2637_, uint8_t v_t_2638_, lean_object* v_h_2639_, lean_object* v_readWrite_2640_){
_start:
{
lean_inc(v_readWrite_2640_);
return v_readWrite_2640_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___boxed(lean_object* v_motive_2641_, lean_object* v_t_2642_, lean_object* v_h_2643_, lean_object* v_readWrite_2644_){
_start:
{
uint8_t v_t_boxed_2645_; lean_object* v_res_2646_; 
v_t_boxed_2645_ = lean_unbox(v_t_2642_);
v_res_2646_ = l_IO_FS_Mode_readWrite_elim(v_motive_2641_, v_t_boxed_2645_, v_h_2643_, v_readWrite_2644_);
lean_dec(v_readWrite_2644_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg(lean_object* v_append_2647_){
_start:
{
lean_inc(v_append_2647_);
return v_append_2647_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg___boxed(lean_object* v_append_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_IO_FS_Mode_append_elim___redArg(v_append_2648_);
lean_dec(v_append_2648_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim(lean_object* v_motive_2650_, uint8_t v_t_2651_, lean_object* v_h_2652_, lean_object* v_append_2653_){
_start:
{
lean_inc(v_append_2653_);
return v_append_2653_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___boxed(lean_object* v_motive_2654_, lean_object* v_t_2655_, lean_object* v_h_2656_, lean_object* v_append_2657_){
_start:
{
uint8_t v_t_boxed_2658_; lean_object* v_res_2659_; 
v_t_boxed_2658_ = lean_unbox(v_t_2655_);
v_res_2659_ = l_IO_FS_Mode_append_elim(v_motive_2654_, v_t_boxed_2658_, v_h_2656_, v_append_2657_);
lean_dec(v_append_2657_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0(){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0___boxed(lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_IO_FS_instInhabitedStream_default___lam__0();
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1(){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1___boxed(lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_IO_FS_instInhabitedStream_default___lam__1();
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2(lean_object* v_x_2673_){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2___boxed(lean_object* v_x_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_IO_FS_instInhabitedStream_default___lam__2(v_x_2677_);
lean_dec_ref(v_x_2677_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3(lean_object* v_x_2680_){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3___boxed(lean_object* v_x_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_IO_FS_instInhabitedStream_default___lam__3(v_x_2684_);
lean_dec_ref(v_x_2684_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4(size_t v_x_2687_){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4___boxed(lean_object* v_x_2691_, lean_object* v___y_2692_){
_start:
{
size_t v_x_193__boxed_2693_; lean_object* v_res_2694_; 
v_x_193__boxed_2693_ = lean_unbox_usize(v_x_2691_);
lean_dec(v_x_2691_);
v_res_2694_ = l_IO_FS_instInhabitedStream_default___lam__4(v_x_193__boxed_2693_);
return v_res_2694_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instInhabitedStream_default___lam__5(uint8_t v___x_2695_){
_start:
{
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__5___boxed(lean_object* v___x_2697_, lean_object* v___y_2698_){
_start:
{
uint8_t v___x_204__boxed_2699_; uint8_t v_res_2700_; lean_object* v_r_2701_; 
v___x_204__boxed_2699_ = lean_unbox(v___x_2697_);
v_res_2700_ = l_IO_FS_instInhabitedStream_default___lam__5(v___x_204__boxed_2699_);
v_r_2701_ = lean_box(v_res_2700_);
return v_r_2701_;
}
}
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object* v_a_00___x40___internal___hyg_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = lean_get_stdin();
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object* v_a_00___x40___internal___hyg_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = lean_get_stdout();
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object* v_a_00___x40___internal___hyg_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = lean_get_stderr();
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object* v_a_00___x40___internal___hyg_2730_, lean_object* v_a_00___x40___internal___hyg_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = lean_get_set_stdin(v_a_00___x40___internal___hyg_2730_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object* v_a_00___x40___internal___hyg_2735_, lean_object* v_a_00___x40___internal___hyg_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = lean_get_set_stdout(v_a_00___x40___internal___hyg_2735_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object* v_a_00___x40___internal___hyg_2740_, lean_object* v_a_00___x40___internal___hyg_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = lean_get_set_stderr(v_a_00___x40___internal___hyg_2740_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_IO_iterate___redArg(lean_object* v_a_2743_, lean_object* v_f_2744_){
_start:
{
lean_object* v___x_2746_; 
lean_inc_ref(v_f_2744_);
v___x_2746_ = lean_apply_2(v_f_2744_, v_a_2743_, lean_box(0));
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2757_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2757_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2757_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
if (lean_obj_tag(v_a_2747_) == 0)
{
lean_object* v_val_2751_; 
lean_del_object(v___x_2749_);
v_val_2751_ = lean_ctor_get(v_a_2747_, 0);
lean_inc(v_val_2751_);
lean_dec_ref_known(v_a_2747_, 1);
v_a_2743_ = v_val_2751_;
goto _start;
}
else
{
lean_object* v_val_2753_; lean_object* v___x_2755_; 
lean_dec_ref(v_f_2744_);
v_val_2753_ = lean_ctor_get(v_a_2747_, 0);
lean_inc(v_val_2753_);
lean_dec_ref_known(v_a_2747_, 1);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v_val_2753_);
v___x_2755_ = v___x_2749_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_val_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec_ref(v_f_2744_);
v_a_2758_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2746_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2746_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_iterate___redArg___boxed(lean_object* v_a_2766_, lean_object* v_f_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_IO_iterate___redArg(v_a_2766_, v_f_2767_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_IO_iterate(lean_object* v_00_u03b1_2770_, lean_object* v_00_u03b2_2771_, lean_object* v_a_2772_, lean_object* v_f_2773_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_IO_iterate___redArg(v_a_2772_, v_f_2773_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_IO_iterate___boxed(lean_object* v_00_u03b1_2776_, lean_object* v_00_u03b2_2777_, lean_object* v_a_2778_, lean_object* v_f_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_IO_iterate(v_00_u03b1_2776_, v_00_u03b2_2777_, v_a_2778_, v_f_2779_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object* v_fn_2785_, lean_object* v_mode_2786_, lean_object* v_a_00___x40___internal___hyg_2787_){
_start:
{
uint8_t v_mode_boxed_2788_; lean_object* v_res_2789_; 
v_mode_boxed_2788_ = lean_unbox(v_mode_2786_);
v_res_2789_ = lean_io_prim_handle_mk(v_fn_2785_, v_mode_boxed_2788_);
lean_dec_ref(v_fn_2785_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lock___boxed(lean_object* v_h_2793_, lean_object* v_exclusive_2794_, lean_object* v_a_00___x40___internal___hyg_2795_){
_start:
{
uint8_t v_exclusive_boxed_2796_; lean_object* v_res_2797_; 
v_exclusive_boxed_2796_ = lean_unbox(v_exclusive_2794_);
v_res_2797_ = lean_io_prim_handle_lock(v_h_2793_, v_exclusive_boxed_2796_);
lean_dec(v_h_2793_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_tryLock___boxed(lean_object* v_h_2801_, lean_object* v_exclusive_2802_, lean_object* v_a_00___x40___internal___hyg_2803_){
_start:
{
uint8_t v_exclusive_boxed_2804_; lean_object* v_res_2805_; 
v_exclusive_boxed_2804_ = lean_unbox(v_exclusive_2802_);
v_res_2805_ = lean_io_prim_handle_try_lock(v_h_2801_, v_exclusive_boxed_2804_);
lean_dec(v_h_2801_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_unlock___boxed(lean_object* v_h_2808_, lean_object* v_a_00___x40___internal___hyg_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = lean_io_prim_handle_unlock(v_h_2808_);
lean_dec(v_h_2808_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_isTty___boxed(lean_object* v_h_2813_, lean_object* v_a_00___x40___internal___hyg_2814_){
_start:
{
uint8_t v_res_2815_; lean_object* v_r_2816_; 
v_res_2815_ = lean_io_prim_handle_is_tty(v_h_2813_);
lean_dec(v_h_2813_);
v_r_2816_ = lean_box(v_res_2815_);
return v_r_2816_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object* v_h_2819_, lean_object* v_a_00___x40___internal___hyg_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = lean_io_prim_handle_flush(v_h_2819_);
lean_dec(v_h_2819_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_rewind___boxed(lean_object* v_h_2824_, lean_object* v_a_00___x40___internal___hyg_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = lean_io_prim_handle_rewind(v_h_2824_);
lean_dec(v_h_2824_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_truncate___boxed(lean_object* v_h_2829_, lean_object* v_a_00___x40___internal___hyg_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = lean_io_prim_handle_truncate(v_h_2829_);
lean_dec(v_h_2829_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_read___boxed(lean_object* v_h_2835_, lean_object* v_bytes_2836_, lean_object* v_a_00___x40___internal___hyg_2837_){
_start:
{
size_t v_bytes_boxed_2838_; lean_object* v_res_2839_; 
v_bytes_boxed_2838_ = lean_unbox_usize(v_bytes_2836_);
lean_dec(v_bytes_2836_);
v_res_2839_ = lean_io_prim_handle_read(v_h_2835_, v_bytes_boxed_2838_);
lean_dec(v_h_2835_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object* v_h_2843_, lean_object* v_buffer_2844_, lean_object* v_a_00___x40___internal___hyg_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = lean_io_prim_handle_write(v_h_2843_, v_buffer_2844_);
lean_dec_ref(v_buffer_2844_);
lean_dec(v_h_2843_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object* v_h_2849_, lean_object* v_a_00___x40___internal___hyg_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = lean_io_prim_handle_get_line(v_h_2849_);
lean_dec(v_h_2849_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object* v_h_2855_, lean_object* v_s_2856_, lean_object* v_a_00___x40___internal___hyg_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = lean_io_prim_handle_put_str(v_h_2855_, v_s_2856_);
lean_dec_ref(v_s_2856_);
lean_dec(v_h_2855_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object* v_fname_2861_, lean_object* v_a_00___x40___internal___hyg_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = lean_io_realpath(v_fname_2861_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object* v_fname_2866_, lean_object* v_a_00___x40___internal___hyg_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = lean_io_remove_file(v_fname_2866_);
lean_dec_ref(v_fname_2866_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object* v_a_00___x40___internal___hyg_2871_, lean_object* v_a_00___x40___internal___hyg_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = lean_io_remove_dir(v_a_00___x40___internal___hyg_2871_);
lean_dec_ref(v_a_00___x40___internal___hyg_2871_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object* v_a_00___x40___internal___hyg_2876_, lean_object* v_a_00___x40___internal___hyg_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = lean_io_create_dir(v_a_00___x40___internal___hyg_2876_);
lean_dec_ref(v_a_00___x40___internal___hyg_2876_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_rename___boxed(lean_object* v_old_2882_, lean_object* v_new_2883_, lean_object* v_a_00___x40___internal___hyg_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = lean_io_rename(v_old_2882_, v_new_2883_);
lean_dec_ref(v_new_2883_);
lean_dec_ref(v_old_2882_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_hardLink___boxed(lean_object* v_orig_2889_, lean_object* v_link_2890_, lean_object* v_a_00___x40___internal___hyg_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = lean_io_hard_link(v_orig_2889_, v_link_2890_);
lean_dec_ref(v_link_2890_);
lean_dec_ref(v_orig_2889_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createTempFile___boxed(lean_object* v_a_00___x40___internal___hyg_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = lean_io_create_tempfile();
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createTempDir___boxed(lean_object* v_a_00___x40___internal___hyg_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = lean_io_create_tempdir();
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object* v_var_2901_, lean_object* v_a_00___x40___internal___hyg_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = lean_io_getenv(v_var_2901_);
lean_dec_ref(v_var_2901_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object* v_a_00___x40___internal___hyg_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = lean_io_app_path();
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object* v_a_00___x40___internal___hyg_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = lean_io_current_dir();
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg(lean_object* v_fn_2910_, uint8_t v_mode_2911_, lean_object* v_f_2912_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = lean_io_prim_handle_mk(v_fn_2910_, v_mode_2911_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
v___x_2916_ = lean_apply_2(v_f_2912_, v_a_2915_, lean_box(0));
return v___x_2916_;
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec_ref(v_f_2912_);
v_a_2917_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2914_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2914_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg___boxed(lean_object* v_fn_2925_, lean_object* v_mode_2926_, lean_object* v_f_2927_, lean_object* v_a_2928_){
_start:
{
uint8_t v_mode_boxed_2929_; lean_object* v_res_2930_; 
v_mode_boxed_2929_ = lean_unbox(v_mode_2926_);
v_res_2930_ = l_IO_FS_withFile___redArg(v_fn_2925_, v_mode_boxed_2929_, v_f_2927_);
lean_dec_ref(v_fn_2925_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object* v_00_u03b1_2931_, lean_object* v_fn_2932_, uint8_t v_mode_2933_, lean_object* v_f_2934_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = lean_io_prim_handle_mk(v_fn_2932_, v_mode_2933_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2938_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
v___x_2938_ = lean_apply_2(v_f_2934_, v_a_2937_, lean_box(0));
return v___x_2938_;
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec_ref(v_f_2934_);
v_a_2939_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2936_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2936_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___boxed(lean_object* v_00_u03b1_2947_, lean_object* v_fn_2948_, lean_object* v_mode_2949_, lean_object* v_f_2950_, lean_object* v_a_2951_){
_start:
{
uint8_t v_mode_boxed_2952_; lean_object* v_res_2953_; 
v_mode_boxed_2952_ = lean_unbox(v_mode_2949_);
v_res_2953_ = l_IO_FS_withFile(v_00_u03b1_2947_, v_fn_2948_, v_mode_boxed_2952_, v_f_2950_);
lean_dec_ref(v_fn_2948_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn(lean_object* v_h_2954_, lean_object* v_s_2955_){
_start:
{
uint32_t v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2957_ = 10;
v___x_2958_ = lean_string_push(v_s_2955_, v___x_2957_);
v___x_2959_ = lean_io_prim_handle_put_str(v_h_2954_, v___x_2958_);
lean_dec_ref(v___x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object* v_h_2960_, lean_object* v_s_2961_, lean_object* v_a_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_IO_FS_Handle_putStrLn(v_h_2960_, v_s_2961_);
lean_dec(v_h_2960_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(lean_object* v_h_2964_, lean_object* v_acc_2965_){
_start:
{
size_t v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = ((size_t)1024ULL);
v___x_2968_ = lean_io_prim_handle_read(v_h_2964_, v___x_2967_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2982_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2971_ = v___x_2968_;
v_isShared_2972_ = v_isSharedCheck_2982_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2968_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2982_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
uint8_t v___x_2973_; 
v___x_2973_ = l_ByteArray_isEmpty(v_a_2969_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_del_object(v___x_2971_);
v___x_2974_ = lean_unsigned_to_nat(0u);
v___x_2975_ = lean_byte_array_size(v_acc_2965_);
v___x_2976_ = lean_byte_array_size(v_a_2969_);
v___x_2977_ = lean_byte_array_copy_slice(v_a_2969_, v___x_2974_, v_acc_2965_, v___x_2975_, v___x_2976_, v___x_2973_);
lean_dec(v_a_2969_);
v_acc_2965_ = v___x_2977_;
goto _start;
}
else
{
lean_object* v___x_2980_; 
lean_dec(v_a_2969_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 0, v_acc_2965_);
v___x_2980_ = v___x_2971_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_acc_2965_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_dec_ref(v_acc_2965_);
return v___x_2968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop___boxed(lean_object* v_h_2983_, lean_object* v_acc_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_2983_, v_acc_2984_);
lean_dec(v_h_2983_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto(lean_object* v_h_2987_, lean_object* v_buf_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_2987_, v_buf_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto___boxed(lean_object* v_h_2991_, lean_object* v_buf_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_IO_FS_Handle_readBinToEndInto(v_h_2991_, v_buf_2992_);
lean_dec(v_h_2991_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object* v_h_2995_){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = l_ByteArray_empty;
v___x_2998_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_2995_, v___x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object* v_h_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_IO_FS_Handle_readBinToEnd(v_h_2999_);
lean_dec(v_h_2999_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object* v_h_3005_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_IO_FS_Handle_readBinToEnd(v_h_3005_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3021_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3021_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3021_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
uint8_t v___x_3012_; 
v___x_3012_ = lean_string_validate_utf8(v_a_3008_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v___x_3015_; 
lean_dec(v_a_3008_);
v___x_3013_ = ((lean_object*)(l_IO_FS_Handle_readToEnd___closed__1));
if (v_isShared_3011_ == 0)
{
lean_ctor_set_tag(v___x_3010_, 1);
lean_ctor_set(v___x_3010_, 0, v___x_3013_);
v___x_3015_ = v___x_3010_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3017_ = lean_string_from_utf8_unchecked(v_a_3008_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3017_);
v___x_3019_ = v___x_3010_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
v_a_3022_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3007_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3007_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object* v_h_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_IO_FS_Handle_readToEnd(v_h_3030_);
lean_dec(v_h_3030_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read(lean_object* v_h_3033_, lean_object* v_lines_3034_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_io_prim_handle_get_line(v_h_3033_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3091_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3039_ = v___x_3036_;
v_isShared_3040_ = v_isSharedCheck_3091_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3036_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3091_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___y_3042_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; uint32_t v___y_3049_; uint32_t v___y_3057_; lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3079_ = lean_string_utf8_byte_size(v_a_3037_);
v___x_3080_ = lean_unsigned_to_nat(0u);
v___x_3081_ = lean_nat_dec_eq(v___x_3079_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
lean_inc(v_a_3037_);
v___x_3082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3082_, 0, v_a_3037_);
lean_ctor_set(v___x_3082_, 1, v___x_3080_);
lean_ctor_set(v___x_3082_, 2, v___x_3079_);
v___x_3083_ = l_String_Slice_Pos_prev_x3f(v___x_3082_, v___x_3079_);
if (lean_obj_tag(v___x_3083_) == 0)
{
uint32_t v___x_3084_; 
lean_dec_ref_known(v___x_3082_, 3);
v___x_3084_ = 65;
v___y_3057_ = v___x_3084_;
goto v___jp_3056_;
}
else
{
lean_object* v_val_3085_; lean_object* v___x_3086_; 
v_val_3085_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_val_3085_);
lean_dec_ref_known(v___x_3083_, 1);
v___x_3086_ = l_String_Slice_Pos_get_x3f(v___x_3082_, v_val_3085_);
lean_dec(v_val_3085_);
lean_dec_ref_known(v___x_3082_, 3);
if (lean_obj_tag(v___x_3086_) == 0)
{
uint32_t v___x_3087_; 
v___x_3087_ = 65;
v___y_3057_ = v___x_3087_;
goto v___jp_3056_;
}
else
{
lean_object* v_val_3088_; uint32_t v___x_3089_; 
v_val_3088_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_val_3088_);
lean_dec_ref_known(v___x_3086_, 1);
v___x_3089_ = lean_unbox_uint32(v_val_3088_);
lean_dec(v_val_3088_);
v___y_3057_ = v___x_3089_;
goto v___jp_3056_;
}
}
}
else
{
lean_object* v___x_3090_; 
lean_del_object(v___x_3039_);
lean_dec(v_a_3037_);
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v_lines_3034_);
return v___x_3090_;
}
v___jp_3041_:
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_array_push(v_lines_3034_, v___y_3042_);
v_lines_3034_ = v___x_3043_;
goto _start;
}
v___jp_3045_:
{
uint32_t v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = 13;
v___x_3051_ = lean_uint32_dec_eq(v___y_3049_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_dec(v___y_3048_);
lean_dec(v___y_3047_);
v___y_3042_ = v___y_3046_;
goto v___jp_3041_;
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3052_ = lean_string_utf8_byte_size(v___y_3046_);
lean_inc(v___y_3048_);
lean_inc_ref(v___y_3046_);
v___x_3053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3053_, 0, v___y_3046_);
lean_ctor_set(v___x_3053_, 1, v___y_3048_);
lean_ctor_set(v___x_3053_, 2, v___x_3052_);
v___x_3054_ = l_String_Slice_Pos_prevn(v___x_3053_, v___x_3052_, v___y_3047_);
lean_dec_ref_known(v___x_3053_, 3);
v___x_3055_ = lean_string_utf8_extract_fast(v___y_3046_, v___y_3048_, v___x_3054_);
lean_dec(v___x_3054_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3046_);
v___y_3042_ = v___x_3055_;
goto v___jp_3041_;
}
}
v___jp_3056_:
{
uint32_t v___x_3058_; uint8_t v___x_3059_; 
v___x_3058_ = 10;
v___x_3059_ = lean_uint32_dec_eq(v___y_3057_, v___x_3058_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3060_ = lean_array_push(v_lines_3034_, v_a_3037_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v___x_3060_);
v___x_3062_ = v___x_3039_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_del_object(v___x_3039_);
v___x_3064_ = lean_unsigned_to_nat(1u);
v___x_3065_ = lean_unsigned_to_nat(0u);
v___x_3066_ = lean_string_utf8_byte_size(v_a_3037_);
lean_inc(v_a_3037_);
v___x_3067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3067_, 0, v_a_3037_);
lean_ctor_set(v___x_3067_, 1, v___x_3065_);
lean_ctor_set(v___x_3067_, 2, v___x_3066_);
v___x_3068_ = l_String_Slice_Pos_prevn(v___x_3067_, v___x_3066_, v___x_3064_);
lean_dec_ref_known(v___x_3067_, 3);
v___x_3069_ = lean_string_utf8_extract_fast(v_a_3037_, v___x_3065_, v___x_3068_);
lean_dec(v___x_3068_);
lean_dec(v_a_3037_);
v___x_3070_ = lean_string_utf8_byte_size(v___x_3069_);
lean_inc_ref(v___x_3069_);
v___x_3071_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3069_);
lean_ctor_set(v___x_3071_, 1, v___x_3065_);
lean_ctor_set(v___x_3071_, 2, v___x_3070_);
v___x_3072_ = l_String_Slice_Pos_prev_x3f(v___x_3071_, v___x_3070_);
if (lean_obj_tag(v___x_3072_) == 0)
{
uint32_t v___x_3073_; 
lean_dec_ref_known(v___x_3071_, 3);
v___x_3073_ = 65;
v___y_3046_ = v___x_3069_;
v___y_3047_ = v___x_3064_;
v___y_3048_ = v___x_3065_;
v___y_3049_ = v___x_3073_;
goto v___jp_3045_;
}
else
{
lean_object* v_val_3074_; lean_object* v___x_3075_; 
v_val_3074_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_val_3074_);
lean_dec_ref_known(v___x_3072_, 1);
v___x_3075_ = l_String_Slice_Pos_get_x3f(v___x_3071_, v_val_3074_);
lean_dec(v_val_3074_);
lean_dec_ref_known(v___x_3071_, 3);
if (lean_obj_tag(v___x_3075_) == 0)
{
uint32_t v___x_3076_; 
v___x_3076_ = 65;
v___y_3046_ = v___x_3069_;
v___y_3047_ = v___x_3064_;
v___y_3048_ = v___x_3065_;
v___y_3049_ = v___x_3076_;
goto v___jp_3045_;
}
else
{
lean_object* v_val_3077_; uint32_t v___x_3078_; 
v_val_3077_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_val_3077_);
lean_dec_ref_known(v___x_3075_, 1);
v___x_3078_ = lean_unbox_uint32(v_val_3077_);
lean_dec(v_val_3077_);
v___y_3046_ = v___x_3069_;
v___y_3047_ = v___x_3064_;
v___y_3048_ = v___x_3065_;
v___y_3049_ = v___x_3078_;
goto v___jp_3045_;
}
}
}
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec_ref(v_lines_3034_);
v_a_3092_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3036_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3036_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read___boxed(lean_object* v_h_3100_, lean_object* v_lines_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_3100_, v_lines_3101_);
lean_dec(v_h_3100_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines(lean_object* v_h_3106_){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_3109_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_3106_, v___x_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines___boxed(lean_object* v_h_3110_, lean_object* v_a_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_IO_FS_Handle_lines(v_h_3110_);
lean_dec(v_h_3110_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object* v_fname_3113_){
_start:
{
uint8_t v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = 0;
v___x_3116_ = lean_io_prim_handle_mk(v_fname_3113_, v___x_3115_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3118_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v___x_3118_ = l_IO_FS_Handle_lines(v_a_3117_);
lean_dec(v_a_3117_);
return v___x_3118_;
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
v_a_3119_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3116_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3116_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object* v_fname_3127_, lean_object* v_a_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_IO_FS_lines(v_fname_3127_);
lean_dec_ref(v_fname_3127_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object* v_fname_3130_, lean_object* v_content_3131_){
_start:
{
uint8_t v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = 1;
v___x_3134_ = lean_io_prim_handle_mk(v_fname_3130_, v___x_3133_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3136_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref_known(v___x_3134_, 1);
v___x_3136_ = lean_io_prim_handle_write(v_a_3135_, v_content_3131_);
lean_dec(v_a_3135_);
return v___x_3136_;
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
v_a_3137_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3134_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3134_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object* v_fname_3145_, lean_object* v_content_3146_, lean_object* v_a_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_IO_FS_writeBinFile(v_fname_3145_, v_content_3146_);
lean_dec_ref(v_content_3146_);
lean_dec_ref(v_fname_3145_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object* v_fname_3149_, lean_object* v_content_3150_){
_start:
{
uint8_t v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = 1;
v___x_3153_ = lean_io_prim_handle_mk(v_fname_3149_, v___x_3152_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3155_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v___x_3155_ = lean_io_prim_handle_put_str(v_a_3154_, v_content_3150_);
lean_dec(v_a_3154_);
return v___x_3155_;
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
v_a_3156_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3153_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3153_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object* v_fname_3164_, lean_object* v_content_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_IO_FS_writeFile(v_fname_3164_, v_content_3165_);
lean_dec_ref(v_content_3165_);
lean_dec_ref(v_fname_3164_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object* v_strm_3168_, lean_object* v_s_3169_){
_start:
{
lean_object* v_putStr_3171_; uint32_t v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_putStr_3171_ = lean_ctor_get(v_strm_3168_, 4);
lean_inc_ref(v_putStr_3171_);
lean_dec_ref(v_strm_3168_);
v___x_3172_ = 10;
v___x_3173_ = lean_string_push(v_s_3169_, v___x_3172_);
v___x_3174_ = lean_apply_2(v_putStr_3171_, v___x_3173_, lean_box(0));
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn___boxed(lean_object* v_strm_3175_, lean_object* v_s_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_IO_FS_Stream_putStrLn(v_strm_3175_, v_s_3176_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00IO_FS_instReprDirEntry_repr_spec__0(lean_object* v_a_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = lean_nat_to_int(v_a_3179_);
return v___x_3180_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = lean_unsigned_to_nat(8u);
v___x_3195_ = lean_nat_to_int(v___x_3194_);
return v___x_3195_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = lean_unsigned_to_nat(12u);
v___x_3206_ = lean_nat_to_int(v___x_3205_);
return v___x_3206_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__0));
v___x_3209_ = lean_string_length(v___x_3208_);
return v___x_3209_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__16, &l_IO_FS_instReprDirEntry_repr___redArg___closed__16_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16);
v___x_3211_ = lean_nat_to_int(v___x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___redArg(lean_object* v_x_3216_){
_start:
{
lean_object* v_root_3217_; lean_object* v_fileName_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3257_; 
v_root_3217_ = lean_ctor_get(v_x_3216_, 0);
v_fileName_3218_ = lean_ctor_get(v_x_3216_, 1);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_x_3216_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3220_ = v_x_3216_;
v_isShared_3221_ = v_isSharedCheck_3257_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_fileName_3218_);
lean_inc(v_root_3217_);
lean_dec(v_x_3216_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3257_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3222_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3223_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__6));
v___x_3224_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3225_ = lean_unsigned_to_nat(0u);
v___x_3226_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__9));
v___x_3227_ = l_String_quote(v_root_3217_);
v___x_3228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set_tag(v___x_3220_, 5);
lean_ctor_set(v___x_3220_, 1, v___x_3228_);
lean_ctor_set(v___x_3220_, 0, v___x_3226_);
v___x_3230_ = v___x_3220_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3226_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___x_3228_);
v___x_3230_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; uint8_t v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3231_ = l_Repr_addAppParen(v___x_3230_, v___x_3225_);
v___x_3232_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3224_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = 0;
v___x_3234_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set_uint8(v___x_3234_, sizeof(void*)*1, v___x_3233_);
v___x_3235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3223_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3235_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
v___x_3238_ = lean_box(1);
v___x_3239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3237_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v___x_3240_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__13));
v___x_3241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3239_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
v___x_3242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
lean_ctor_set(v___x_3242_, 1, v___x_3222_);
v___x_3243_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__14, &l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14);
v___x_3244_ = l_String_quote(v_fileName_3218_);
v___x_3245_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
v___x_3246_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3243_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
lean_ctor_set_uint8(v___x_3247_, sizeof(void*)*1, v___x_3233_);
v___x_3248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3242_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3250_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
lean_ctor_set(v___x_3251_, 1, v___x_3248_);
v___x_3252_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3251_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3249_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
lean_ctor_set_uint8(v___x_3255_, sizeof(void*)*1, v___x_3233_);
return v___x_3255_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr(lean_object* v_x_3258_, lean_object* v_prec_3259_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_IO_FS_instReprDirEntry_repr___redArg(v_x_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___boxed(lean_object* v_x_3261_, lean_object* v_prec_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_IO_FS_instReprDirEntry_repr(v_x_3261_, v_prec_3262_);
lean_dec(v_prec_3262_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object* v_entry_3266_){
_start:
{
lean_object* v_root_3267_; lean_object* v_fileName_3268_; lean_object* v___x_3269_; 
v_root_3267_ = lean_ctor_get(v_entry_3266_, 0);
lean_inc_ref(v_root_3267_);
v_fileName_3268_ = lean_ctor_get(v_entry_3266_, 1);
lean_inc_ref(v_fileName_3268_);
lean_dec_ref(v_entry_3266_);
v___x_3269_ = l_System_FilePath_join(v_root_3267_, v_fileName_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx(uint8_t v_x_3270_){
_start:
{
switch(v_x_3270_)
{
case 0:
{
lean_object* v___x_3271_; 
v___x_3271_ = lean_unsigned_to_nat(0u);
return v___x_3271_;
}
case 1:
{
lean_object* v___x_3272_; 
v___x_3272_ = lean_unsigned_to_nat(1u);
return v___x_3272_;
}
case 2:
{
lean_object* v___x_3273_; 
v___x_3273_ = lean_unsigned_to_nat(2u);
return v___x_3273_;
}
default: 
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_unsigned_to_nat(3u);
return v___x_3274_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx___boxed(lean_object* v_x_3275_){
_start:
{
uint8_t v_x_boxed_3276_; lean_object* v_res_3277_; 
v_x_boxed_3276_ = lean_unbox(v_x_3275_);
v_res_3277_ = l_IO_FS_FileType_ctorIdx(v_x_boxed_3276_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg(lean_object* v_k_3278_){
_start:
{
lean_inc(v_k_3278_);
return v_k_3278_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg___boxed(lean_object* v_k_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_IO_FS_FileType_ctorElim___redArg(v_k_3279_);
lean_dec(v_k_3279_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim(lean_object* v_motive_3281_, lean_object* v_ctorIdx_3282_, uint8_t v_t_3283_, lean_object* v_h_3284_, lean_object* v_k_3285_){
_start:
{
lean_inc(v_k_3285_);
return v_k_3285_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___boxed(lean_object* v_motive_3286_, lean_object* v_ctorIdx_3287_, lean_object* v_t_3288_, lean_object* v_h_3289_, lean_object* v_k_3290_){
_start:
{
uint8_t v_t_boxed_3291_; lean_object* v_res_3292_; 
v_t_boxed_3291_ = lean_unbox(v_t_3288_);
v_res_3292_ = l_IO_FS_FileType_ctorElim(v_motive_3286_, v_ctorIdx_3287_, v_t_boxed_3291_, v_h_3289_, v_k_3290_);
lean_dec(v_k_3290_);
lean_dec(v_ctorIdx_3287_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg(lean_object* v_dir_3293_){
_start:
{
lean_inc(v_dir_3293_);
return v_dir_3293_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg___boxed(lean_object* v_dir_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_IO_FS_FileType_dir_elim___redArg(v_dir_3294_);
lean_dec(v_dir_3294_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim(lean_object* v_motive_3296_, uint8_t v_t_3297_, lean_object* v_h_3298_, lean_object* v_dir_3299_){
_start:
{
lean_inc(v_dir_3299_);
return v_dir_3299_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___boxed(lean_object* v_motive_3300_, lean_object* v_t_3301_, lean_object* v_h_3302_, lean_object* v_dir_3303_){
_start:
{
uint8_t v_t_boxed_3304_; lean_object* v_res_3305_; 
v_t_boxed_3304_ = lean_unbox(v_t_3301_);
v_res_3305_ = l_IO_FS_FileType_dir_elim(v_motive_3300_, v_t_boxed_3304_, v_h_3302_, v_dir_3303_);
lean_dec(v_dir_3303_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg(lean_object* v_file_3306_){
_start:
{
lean_inc(v_file_3306_);
return v_file_3306_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg___boxed(lean_object* v_file_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_IO_FS_FileType_file_elim___redArg(v_file_3307_);
lean_dec(v_file_3307_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim(lean_object* v_motive_3309_, uint8_t v_t_3310_, lean_object* v_h_3311_, lean_object* v_file_3312_){
_start:
{
lean_inc(v_file_3312_);
return v_file_3312_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___boxed(lean_object* v_motive_3313_, lean_object* v_t_3314_, lean_object* v_h_3315_, lean_object* v_file_3316_){
_start:
{
uint8_t v_t_boxed_3317_; lean_object* v_res_3318_; 
v_t_boxed_3317_ = lean_unbox(v_t_3314_);
v_res_3318_ = l_IO_FS_FileType_file_elim(v_motive_3313_, v_t_boxed_3317_, v_h_3315_, v_file_3316_);
lean_dec(v_file_3316_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg(lean_object* v_symlink_3319_){
_start:
{
lean_inc(v_symlink_3319_);
return v_symlink_3319_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg___boxed(lean_object* v_symlink_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_IO_FS_FileType_symlink_elim___redArg(v_symlink_3320_);
lean_dec(v_symlink_3320_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim(lean_object* v_motive_3322_, uint8_t v_t_3323_, lean_object* v_h_3324_, lean_object* v_symlink_3325_){
_start:
{
lean_inc(v_symlink_3325_);
return v_symlink_3325_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___boxed(lean_object* v_motive_3326_, lean_object* v_t_3327_, lean_object* v_h_3328_, lean_object* v_symlink_3329_){
_start:
{
uint8_t v_t_boxed_3330_; lean_object* v_res_3331_; 
v_t_boxed_3330_ = lean_unbox(v_t_3327_);
v_res_3331_ = l_IO_FS_FileType_symlink_elim(v_motive_3326_, v_t_boxed_3330_, v_h_3328_, v_symlink_3329_);
lean_dec(v_symlink_3329_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg(lean_object* v_other_3332_){
_start:
{
lean_inc(v_other_3332_);
return v_other_3332_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg___boxed(lean_object* v_other_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_IO_FS_FileType_other_elim___redArg(v_other_3333_);
lean_dec(v_other_3333_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim(lean_object* v_motive_3335_, uint8_t v_t_3336_, lean_object* v_h_3337_, lean_object* v_other_3338_){
_start:
{
lean_inc(v_other_3338_);
return v_other_3338_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___boxed(lean_object* v_motive_3339_, lean_object* v_t_3340_, lean_object* v_h_3341_, lean_object* v_other_3342_){
_start:
{
uint8_t v_t_boxed_3343_; lean_object* v_res_3344_; 
v_t_boxed_3343_ = lean_unbox(v_t_3340_);
v_res_3344_ = l_IO_FS_FileType_other_elim(v_motive_3339_, v_t_boxed_3343_, v_h_3341_, v_other_3342_);
lean_dec(v_other_3342_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr(uint8_t v_x_3357_, lean_object* v_prec_3358_){
_start:
{
lean_object* v___y_3360_; lean_object* v___y_3367_; lean_object* v___y_3374_; lean_object* v___y_3381_; 
switch(v_x_3357_)
{
case 0:
{
lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3387_ = lean_unsigned_to_nat(1024u);
v___x_3388_ = lean_nat_dec_le(v___x_3387_, v_prec_3358_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; 
v___x_3389_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3360_ = v___x_3389_;
goto v___jp_3359_;
}
else
{
lean_object* v___x_3390_; 
v___x_3390_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3360_ = v___x_3390_;
goto v___jp_3359_;
}
}
case 1:
{
lean_object* v___x_3391_; uint8_t v___x_3392_; 
v___x_3391_ = lean_unsigned_to_nat(1024u);
v___x_3392_ = lean_nat_dec_le(v___x_3391_, v_prec_3358_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; 
v___x_3393_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3367_ = v___x_3393_;
goto v___jp_3366_;
}
else
{
lean_object* v___x_3394_; 
v___x_3394_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3367_ = v___x_3394_;
goto v___jp_3366_;
}
}
case 2:
{
lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3395_ = lean_unsigned_to_nat(1024u);
v___x_3396_ = lean_nat_dec_le(v___x_3395_, v_prec_3358_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; 
v___x_3397_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3374_ = v___x_3397_;
goto v___jp_3373_;
}
else
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3374_ = v___x_3398_;
goto v___jp_3373_;
}
}
default: 
{
lean_object* v___x_3399_; uint8_t v___x_3400_; 
v___x_3399_ = lean_unsigned_to_nat(1024u);
v___x_3400_ = lean_nat_dec_le(v___x_3399_, v_prec_3358_);
if (v___x_3400_ == 0)
{
lean_object* v___x_3401_; 
v___x_3401_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3381_ = v___x_3401_;
goto v___jp_3380_;
}
else
{
lean_object* v___x_3402_; 
v___x_3402_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3381_ = v___x_3402_;
goto v___jp_3380_;
}
}
}
v___jp_3359_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3361_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__1));
lean_inc(v___y_3360_);
v___x_3362_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___y_3360_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = 0;
v___x_3364_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3364_, 0, v___x_3362_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*1, v___x_3363_);
v___x_3365_ = l_Repr_addAppParen(v___x_3364_, v_prec_3358_);
return v___x_3365_;
}
v___jp_3366_:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3368_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__3));
lean_inc(v___y_3367_);
v___x_3369_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___y_3367_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___x_3370_ = 0;
v___x_3371_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3371_, 0, v___x_3369_);
lean_ctor_set_uint8(v___x_3371_, sizeof(void*)*1, v___x_3370_);
v___x_3372_ = l_Repr_addAppParen(v___x_3371_, v_prec_3358_);
return v___x_3372_;
}
v___jp_3373_:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3375_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__5));
lean_inc(v___y_3374_);
v___x_3376_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___y_3374_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = 0;
v___x_3378_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3378_, 0, v___x_3376_);
lean_ctor_set_uint8(v___x_3378_, sizeof(void*)*1, v___x_3377_);
v___x_3379_ = l_Repr_addAppParen(v___x_3378_, v_prec_3358_);
return v___x_3379_;
}
v___jp_3380_:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3382_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__7));
lean_inc(v___y_3381_);
v___x_3383_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___y_3381_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = 0;
v___x_3385_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3385_, 0, v___x_3383_);
lean_ctor_set_uint8(v___x_3385_, sizeof(void*)*1, v___x_3384_);
v___x_3386_ = l_Repr_addAppParen(v___x_3385_, v_prec_3358_);
return v___x_3386_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr___boxed(lean_object* v_x_3403_, lean_object* v_prec_3404_){
_start:
{
uint8_t v_x_229__boxed_3405_; lean_object* v_res_3406_; 
v_x_229__boxed_3405_ = lean_unbox(v_x_3403_);
v_res_3406_ = l_IO_FS_instReprFileType_repr(v_x_229__boxed_3405_, v_prec_3404_);
lean_dec(v_prec_3404_);
return v_res_3406_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instBEqFileType_beq(uint8_t v_x_3409_, uint8_t v_y_3410_){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; 
v___x_3411_ = l_IO_FS_FileType_ctorIdx(v_x_3409_);
v___x_3412_ = l_IO_FS_FileType_ctorIdx(v_y_3410_);
v___x_3413_ = lean_nat_dec_eq(v___x_3411_, v___x_3412_);
lean_dec(v___x_3412_);
lean_dec(v___x_3411_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType_beq___boxed(lean_object* v_x_3414_, lean_object* v_y_3415_){
_start:
{
uint8_t v_x_17__boxed_3416_; uint8_t v_y_18__boxed_3417_; uint8_t v_res_3418_; lean_object* v_r_3419_; 
v_x_17__boxed_3416_ = lean_unbox(v_x_3414_);
v_y_18__boxed_3417_ = lean_unbox(v_y_3415_);
v_res_3418_ = l_IO_FS_instBEqFileType_beq(v_x_17__boxed_3416_, v_y_18__boxed_3417_);
v_r_3419_ = lean_box(v_res_3418_);
return v_r_3419_;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = lean_unsigned_to_nat(7u);
v___x_3432_ = lean_nat_to_int(v___x_3431_);
return v___x_3432_;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = lean_unsigned_to_nat(0u);
v___x_3437_ = lean_nat_to_int(v___x_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object* v_x_3438_){
_start:
{
lean_object* v_sec_3439_; uint32_t v_nsec_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___y_3445_; lean_object* v___x_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
v_sec_3439_ = lean_ctor_get(v_x_3438_, 0);
v_nsec_3440_ = lean_ctor_get_uint32(v_x_3438_, sizeof(void*)*1);
v___x_3441_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3442_ = ((lean_object*)(l_IO_FS_instReprSystemTime_repr___redArg___closed__3));
v___x_3443_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__4, &l_IO_FS_instReprSystemTime_repr___redArg___closed__4_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4);
v___x_3471_ = lean_unsigned_to_nat(0u);
v___x_3472_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__7, &l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7);
v___x_3473_ = lean_int_dec_lt(v_sec_3439_, v___x_3472_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = l_Int_repr(v_sec_3439_);
v___x_3475_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
v___y_3445_ = v___x_3475_;
goto v___jp_3444_;
}
else
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3476_ = l_Int_repr(v_sec_3439_);
v___x_3477_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
v___x_3478_ = l_Repr_addAppParen(v___x_3477_, v___x_3471_);
v___y_3445_ = v___x_3478_;
goto v___jp_3444_;
}
v___jp_3444_:
{
lean_object* v___x_3446_; uint8_t v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3446_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3443_);
lean_ctor_set(v___x_3446_, 1, v___y_3445_);
v___x_3447_ = 0;
v___x_3448_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3448_, 0, v___x_3446_);
lean_ctor_set_uint8(v___x_3448_, sizeof(void*)*1, v___x_3447_);
v___x_3449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3442_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3449_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
v___x_3452_ = lean_box(1);
v___x_3453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3451_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
v___x_3454_ = ((lean_object*)(l_IO_FS_instReprSystemTime_repr___redArg___closed__6));
v___x_3455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3453_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
v___x_3456_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3455_);
lean_ctor_set(v___x_3456_, 1, v___x_3441_);
v___x_3457_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3458_ = lean_uint32_to_nat(v_nsec_3440_);
v___x_3459_ = l_Nat_reprFast(v___x_3458_);
v___x_3460_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
v___x_3461_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3457_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
v___x_3462_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3462_, 0, v___x_3461_);
lean_ctor_set_uint8(v___x_3462_, sizeof(void*)*1, v___x_3447_);
v___x_3463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3456_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
v___x_3464_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3465_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
lean_ctor_set(v___x_3466_, 1, v___x_3463_);
v___x_3467_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3468_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3466_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3464_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*1, v___x_3447_);
return v___x_3470_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg___boxed(lean_object* v_x_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_3479_);
lean_dec_ref(v_x_3479_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr(lean_object* v_x_3481_, lean_object* v_prec_3482_){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_3481_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___boxed(lean_object* v_x_3484_, lean_object* v_prec_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_IO_FS_instReprSystemTime_repr(v_x_3484_, v_prec_3485_);
lean_dec(v_prec_3485_);
lean_dec_ref(v_x_3484_);
return v_res_3486_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instBEqSystemTime_beq(lean_object* v_x_3489_, lean_object* v_x_3490_){
_start:
{
lean_object* v_sec_3491_; uint32_t v_nsec_3492_; lean_object* v_sec_3493_; uint32_t v_nsec_3494_; uint8_t v___x_3495_; 
v_sec_3491_ = lean_ctor_get(v_x_3489_, 0);
v_nsec_3492_ = lean_ctor_get_uint32(v_x_3489_, sizeof(void*)*1);
v_sec_3493_ = lean_ctor_get(v_x_3490_, 0);
v_nsec_3494_ = lean_ctor_get_uint32(v_x_3490_, sizeof(void*)*1);
v___x_3495_ = lean_int_dec_eq(v_sec_3491_, v_sec_3493_);
if (v___x_3495_ == 0)
{
return v___x_3495_;
}
else
{
uint8_t v___x_3496_; 
v___x_3496_ = lean_uint32_dec_eq(v_nsec_3492_, v_nsec_3494_);
return v___x_3496_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime_beq___boxed(lean_object* v_x_3497_, lean_object* v_x_3498_){
_start:
{
uint8_t v_res_3499_; lean_object* v_r_3500_; 
v_res_3499_ = l_IO_FS_instBEqSystemTime_beq(v_x_3497_, v_x_3498_);
lean_dec_ref(v_x_3498_);
lean_dec_ref(v_x_3497_);
v_r_3500_ = lean_box(v_res_3499_);
return v_r_3500_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object* v_x_3503_, lean_object* v_x_3504_){
_start:
{
lean_object* v_sec_3505_; uint32_t v_nsec_3506_; lean_object* v_sec_3507_; uint32_t v_nsec_3508_; uint8_t v___x_3509_; 
v_sec_3505_ = lean_ctor_get(v_x_3503_, 0);
v_nsec_3506_ = lean_ctor_get_uint32(v_x_3503_, sizeof(void*)*1);
v_sec_3507_ = lean_ctor_get(v_x_3504_, 0);
v_nsec_3508_ = lean_ctor_get_uint32(v_x_3504_, sizeof(void*)*1);
v___x_3509_ = lean_int_dec_lt(v_sec_3505_, v_sec_3507_);
if (v___x_3509_ == 0)
{
uint8_t v___x_3510_; 
v___x_3510_ = lean_int_dec_eq(v_sec_3505_, v_sec_3507_);
if (v___x_3510_ == 0)
{
uint8_t v___x_3511_; 
v___x_3511_ = 2;
return v___x_3511_;
}
else
{
uint8_t v___x_3512_; 
v___x_3512_ = lean_uint32_dec_lt(v_nsec_3506_, v_nsec_3508_);
if (v___x_3512_ == 0)
{
uint8_t v___x_3513_; 
v___x_3513_ = lean_uint32_dec_eq(v_nsec_3506_, v_nsec_3508_);
if (v___x_3513_ == 0)
{
uint8_t v___x_3514_; 
v___x_3514_ = 2;
return v___x_3514_;
}
else
{
uint8_t v___x_3515_; 
v___x_3515_ = 1;
return v___x_3515_;
}
}
else
{
uint8_t v___x_3516_; 
v___x_3516_ = 0;
return v___x_3516_;
}
}
}
else
{
uint8_t v___x_3517_; 
v___x_3517_ = 0;
return v___x_3517_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime_ord___boxed(lean_object* v_x_3518_, lean_object* v_x_3519_){
_start:
{
uint8_t v_res_3520_; lean_object* v_r_3521_; 
v_res_3520_ = l_IO_FS_instOrdSystemTime_ord(v_x_3518_, v_x_3519_);
lean_dec_ref(v_x_3519_);
lean_dec_ref(v_x_3518_);
v_r_3521_ = lean_box(v_res_3520_);
return v_r_3521_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default___closed__0(void){
_start:
{
uint32_t v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3524_ = 0;
v___x_3525_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__7, &l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7);
v___x_3526_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
lean_ctor_set_uint32(v___x_3526_, sizeof(void*)*1, v___x_3524_);
return v___x_3526_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default(void){
_start:
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_obj_once(&l_IO_FS_instInhabitedSystemTime_default___closed__0, &l_IO_FS_instInhabitedSystemTime_default___closed__0_once, _init_l_IO_FS_instInhabitedSystemTime_default___closed__0);
return v___x_3527_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime(void){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_IO_FS_instInhabitedSystemTime_default;
return v___x_3528_;
}
}
static lean_object* _init_l_IO_FS_instLTSystemTime(void){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_box(0);
return v___x_3529_;
}
}
static lean_object* _init_l_IO_FS_instLESystemTime(void){
_start:
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_box(0);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg(lean_object* v_x_3552_){
_start:
{
lean_object* v_accessed_3553_; lean_object* v_modified_3554_; uint64_t v_byteSize_3555_; uint8_t v_type_3556_; uint64_t v_numLinks_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v_accessed_3553_ = lean_ctor_get(v_x_3552_, 0);
v_modified_3554_ = lean_ctor_get(v_x_3552_, 1);
v_byteSize_3555_ = lean_ctor_get_uint64(v_x_3552_, sizeof(void*)*2);
v_type_3556_ = lean_ctor_get_uint8(v_x_3552_, sizeof(void*)*2 + 16);
v_numLinks_3557_ = lean_ctor_get_uint64(v_x_3552_, sizeof(void*)*2 + 8);
v___x_3558_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3559_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__3));
v___x_3560_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__14, &l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14);
v___x_3561_ = lean_unsigned_to_nat(0u);
v___x_3562_ = l_IO_FS_instReprSystemTime_repr___redArg(v_accessed_3553_);
v___x_3563_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3560_);
lean_ctor_set(v___x_3563_, 1, v___x_3562_);
v___x_3564_ = 0;
v___x_3565_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3565_, 0, v___x_3563_);
lean_ctor_set_uint8(v___x_3565_, sizeof(void*)*1, v___x_3564_);
v___x_3566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3559_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = lean_box(1);
v___x_3570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3568_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__5));
v___x_3572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3570_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
lean_ctor_set(v___x_3573_, 1, v___x_3558_);
v___x_3574_ = l_IO_FS_instReprSystemTime_repr___redArg(v_modified_3554_);
v___x_3575_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3560_);
lean_ctor_set(v___x_3575_, 1, v___x_3574_);
v___x_3576_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
lean_ctor_set_uint8(v___x_3576_, sizeof(void*)*1, v___x_3564_);
v___x_3577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3573_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
v___x_3578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
lean_ctor_set(v___x_3578_, 1, v___x_3567_);
v___x_3579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3578_);
lean_ctor_set(v___x_3579_, 1, v___x_3569_);
v___x_3580_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__7));
v___x_3581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3579_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
lean_ctor_set(v___x_3582_, 1, v___x_3558_);
v___x_3583_ = lean_uint64_to_nat(v_byteSize_3555_);
v___x_3584_ = l_Nat_reprFast(v___x_3583_);
v___x_3585_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
v___x_3586_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3560_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
lean_ctor_set_uint8(v___x_3587_, sizeof(void*)*1, v___x_3564_);
v___x_3588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3582_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
v___x_3589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
lean_ctor_set(v___x_3589_, 1, v___x_3567_);
v___x_3590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
lean_ctor_set(v___x_3590_, 1, v___x_3569_);
v___x_3591_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__9));
v___x_3592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3590_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
v___x_3593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
lean_ctor_set(v___x_3593_, 1, v___x_3558_);
v___x_3594_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3595_ = l_IO_FS_instReprFileType_repr(v_type_3556_, v___x_3561_);
v___x_3596_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3594_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
lean_ctor_set_uint8(v___x_3597_, sizeof(void*)*1, v___x_3564_);
v___x_3598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3593_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
lean_ctor_set(v___x_3599_, 1, v___x_3567_);
v___x_3600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
lean_ctor_set(v___x_3600_, 1, v___x_3569_);
v___x_3601_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__11));
v___x_3602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3600_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
lean_ctor_set(v___x_3603_, 1, v___x_3558_);
v___x_3604_ = lean_uint64_to_nat(v_numLinks_3557_);
v___x_3605_ = l_Nat_reprFast(v___x_3604_);
v___x_3606_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
v___x_3607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3560_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set_uint8(v___x_3608_, sizeof(void*)*1, v___x_3564_);
v___x_3609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3603_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3611_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
lean_ctor_set(v___x_3612_, 1, v___x_3609_);
v___x_3613_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3612_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3610_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
lean_ctor_set_uint8(v___x_3616_, sizeof(void*)*1, v___x_3564_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg___boxed(lean_object* v_x_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_3617_);
lean_dec_ref(v_x_3617_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr(lean_object* v_x_3619_, lean_object* v_prec_3620_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_3619_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___boxed(lean_object* v_x_3622_, lean_object* v_prec_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_IO_FS_instReprMetadata_repr(v_x_3622_, v_prec_3623_);
lean_dec(v_prec_3623_);
lean_dec_ref(v_x_3622_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object* v_a_00___x40___internal___hyg_3629_, lean_object* v_a_00___x40___internal___hyg_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = lean_io_read_dir(v_a_00___x40___internal___hyg_3629_);
lean_dec_ref(v_a_00___x40___internal___hyg_3629_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object* v_a_00___x40___internal___hyg_3634_, lean_object* v_a_00___x40___internal___hyg_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = lean_io_metadata(v_a_00___x40___internal___hyg_3634_);
lean_dec_ref(v_a_00___x40___internal___hyg_3634_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_symlinkMetadata___boxed(lean_object* v_a_00___x40___internal___hyg_3639_, lean_object* v_a_00___x40___internal___hyg_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = lean_io_symlink_metadata(v_a_00___x40___internal___hyg_3639_);
lean_dec_ref(v_a_00___x40___internal___hyg_3639_);
return v_res_3641_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isDir(lean_object* v_p_3642_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = lean_io_metadata(v_p_3642_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; uint8_t v_type_3646_; uint8_t v___x_3647_; uint8_t v___x_3648_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3644_, 1);
v_type_3646_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*2 + 16);
lean_dec(v_a_3645_);
v___x_3647_ = 0;
v___x_3648_ = l_IO_FS_instBEqFileType_beq(v_type_3646_, v___x_3647_);
return v___x_3648_;
}
else
{
uint8_t v___x_3649_; 
lean_dec_ref_known(v___x_3644_, 1);
v___x_3649_ = 0;
return v___x_3649_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object* v_p_3650_, lean_object* v_a_3651_){
_start:
{
uint8_t v_res_3652_; lean_object* v_r_3653_; 
v_res_3652_ = l_System_FilePath_isDir(v_p_3650_);
lean_dec_ref(v_p_3650_);
v_r_3653_ = lean_box(v_res_3652_);
return v_r_3653_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_pathExists(lean_object* v_p_3654_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = lean_io_metadata(v_p_3654_);
if (lean_obj_tag(v___x_3656_) == 0)
{
uint8_t v___x_3657_; 
lean_dec_ref_known(v___x_3656_, 1);
v___x_3657_ = 1;
return v___x_3657_;
}
else
{
uint8_t v___x_3658_; 
lean_dec_ref_known(v___x_3656_, 1);
v___x_3658_ = 0;
return v___x_3658_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object* v_p_3659_, lean_object* v_a_3660_){
_start:
{
uint8_t v_res_3661_; lean_object* v_r_3662_; 
v_res_3661_ = l_System_FilePath_pathExists(v_p_3659_);
lean_dec_ref(v_p_3659_);
v_r_3662_ = lean_box(v_res_3661_);
return v_r_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(lean_object* v_enter_3663_, lean_object* v_p_3664_, lean_object* v_as_3665_, size_t v_sz_3666_, size_t v_i_3667_, lean_object* v_b_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v_a_3672_; lean_object* v_snd_3673_; uint8_t v___x_3677_; 
v___x_3677_ = lean_usize_dec_lt(v_i_3667_, v_sz_3666_);
if (v___x_3677_ == 0)
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
lean_dec_ref(v_p_3664_);
lean_dec_ref(v_enter_3663_);
v___x_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3678_, 0, v_b_3668_);
lean_ctor_set(v___x_3678_, 1, v___y_3669_);
v___x_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
return v___x_3679_;
}
else
{
lean_object* v___x_3680_; lean_object* v_a_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3680_ = lean_box(0);
v_a_3681_ = lean_array_uget_borrowed(v_as_3665_, v_i_3667_);
lean_inc(v_a_3681_);
v___x_3682_ = l_IO_FS_DirEntry_path(v_a_3681_);
lean_inc_ref(v___x_3682_);
v___x_3683_ = lean_array_push(v___y_3669_, v___x_3682_);
v___x_3684_ = lean_io_metadata(v___x_3682_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; uint8_t v_type_3686_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3685_);
lean_dec_ref_known(v___x_3684_, 1);
v_type_3686_ = lean_ctor_get_uint8(v_a_3685_, sizeof(void*)*2 + 16);
lean_dec(v_a_3685_);
switch(v_type_3686_)
{
case 2:
{
lean_object* v___x_3687_; 
v___x_3687_ = lean_io_realpath(v___x_3682_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; uint8_t v___x_3689_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v___x_3687_, 1);
v___x_3689_ = l_System_FilePath_isDir(v_a_3688_);
if (v___x_3689_ == 0)
{
lean_dec(v_a_3688_);
v_a_3672_ = v___x_3680_;
v_snd_3673_ = v___x_3683_;
goto v___jp_3671_;
}
else
{
lean_object* v___x_3690_; 
lean_inc_ref(v_enter_3663_);
lean_inc_ref(v_p_3664_);
v___x_3690_ = lean_apply_2(v_enter_3663_, v_p_3664_, lean_box(0));
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; uint8_t v___x_3692_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref_known(v___x_3690_, 1);
v___x_3692_ = lean_unbox(v_a_3691_);
lean_dec(v_a_3691_);
if (v___x_3692_ == 0)
{
lean_dec(v_a_3688_);
v_a_3672_ = v___x_3680_;
v_snd_3673_ = v___x_3683_;
goto v___jp_3671_;
}
else
{
lean_object* v___x_3693_; 
lean_inc_ref(v_enter_3663_);
v___x_3693_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3663_, v_a_3688_, v___x_3683_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v_snd_3695_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
v_snd_3695_ = lean_ctor_get(v_a_3694_, 1);
lean_inc(v_snd_3695_);
lean_dec(v_a_3694_);
v_a_3672_ = v___x_3680_;
v_snd_3673_ = v_snd_3695_;
goto v___jp_3671_;
}
else
{
lean_dec_ref(v_p_3664_);
lean_dec_ref(v_enter_3663_);
return v___x_3693_;
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec(v_a_3688_);
lean_dec_ref(v___x_3683_);
lean_dec_ref(v_p_3664_);
lean_dec_ref(v_enter_3663_);
v_a_3696_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3690_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3690_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec_ref(v___x_3683_);
lean_dec_ref(v_p_3664_);
lean_dec_ref(v_enter_3663_);
v_a_3704_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3687_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3687_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
case 0:
{
lean_object* v___x_3712_; 
lean_inc_ref(v_enter_3663_);
v___x_3712_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3663_, v___x_3682_, v___x_3683_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v_snd_3714_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3712_, 1);
v_snd_3714_ = lean_ctor_get(v_a_3713_, 1);
lean_inc(v_snd_3714_);
lean_dec(v_a_3713_);
v_a_3672_ = v___x_3680_;
v_snd_3673_ = v_snd_3714_;
goto v___jp_3671_;
}
else
{
lean_dec_ref(v_p_3664_);
lean_dec_ref(v_enter_3663_);
return v___x_3712_;
}
}
default: 
{
lean_dec_ref(v___x_3682_);
v_a_3672_ = v___x_3680_;
v_snd_3673_ = v___x_3683_;
goto v___jp_3671_;
}
}
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec_ref(v___x_3682_);
v_a_3715_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3684_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3684_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
if (lean_obj_tag(v_a_3715_) == 11)
{
lean_dec_ref_known(v_a_3715_, 2);
lean_del_object(v___x_3717_);
v_a_3672_ = v___x_3680_;
v_snd_3673_ = v___x_3683_;
goto v___jp_3671_;
}
else
{
lean_object* v___x_3720_; 
lean_dec_ref(v___x_3683_);
lean_dec_ref(v_p_3664_);
lean_dec_ref(v_enter_3663_);
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
v___jp_3671_:
{
size_t v___x_3674_; size_t v___x_3675_; 
v___x_3674_ = ((size_t)1ULL);
v___x_3675_ = lean_usize_add(v_i_3667_, v___x_3674_);
v_i_3667_ = v___x_3675_;
v_b_3668_ = v_a_3672_;
v___y_3669_ = v_snd_3673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go(lean_object* v_enter_3723_, lean_object* v_p_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v___x_3727_; 
lean_inc_ref(v_enter_3723_);
lean_inc_ref(v_p_3724_);
v___x_3727_ = lean_apply_2(v_enter_3723_, v_p_3724_, lean_box(0));
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3769_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3730_ = v___x_3727_;
v_isShared_3731_ = v_isSharedCheck_3769_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3727_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3769_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
uint8_t v___x_3732_; 
v___x_3732_ = lean_unbox(v_a_3728_);
lean_dec(v_a_3728_);
if (v___x_3732_ == 0)
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3736_; 
lean_dec_ref(v_p_3724_);
lean_dec_ref(v_enter_3723_);
v___x_3733_ = lean_box(0);
v___x_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
lean_ctor_set(v___x_3734_, 1, v_a_3725_);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 0, v___x_3734_);
v___x_3736_ = v___x_3730_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3734_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
else
{
lean_object* v___x_3738_; 
lean_del_object(v___x_3730_);
v___x_3738_ = lean_io_read_dir(v_p_3724_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3740_; size_t v_sz_3741_; size_t v___x_3742_; lean_object* v___x_3743_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_a_3739_);
lean_dec_ref_known(v___x_3738_, 1);
v___x_3740_ = lean_box(0);
v_sz_3741_ = lean_array_size(v_a_3739_);
v___x_3742_ = ((size_t)0ULL);
v___x_3743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_3723_, v_p_3724_, v_a_3739_, v_sz_3741_, v___x_3742_, v___x_3740_, v_a_3725_);
lean_dec(v_a_3739_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3760_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3746_ = v___x_3743_;
v_isShared_3747_ = v_isSharedCheck_3760_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3743_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3760_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v_snd_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3758_; 
v_snd_3748_ = lean_ctor_get(v_a_3744_, 1);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_a_3744_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; 
v_unused_3759_ = lean_ctor_get(v_a_3744_, 0);
lean_dec(v_unused_3759_);
v___x_3750_ = v_a_3744_;
v_isShared_3751_ = v_isSharedCheck_3758_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_snd_3748_);
lean_dec(v_a_3744_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3758_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v___x_3740_);
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3740_);
lean_ctor_set(v_reuseFailAlloc_3757_, 1, v_snd_3748_);
v___x_3753_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
lean_object* v___x_3755_; 
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 0, v___x_3753_);
v___x_3755_ = v___x_3746_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3753_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
else
{
return v___x_3743_;
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec_ref(v_a_3725_);
lean_dec_ref(v_p_3724_);
lean_dec_ref(v_enter_3723_);
v_a_3761_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3738_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3738_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec_ref(v_a_3725_);
lean_dec_ref(v_p_3724_);
lean_dec_ref(v_enter_3723_);
v_a_3770_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3727_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3727_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go___boxed(lean_object* v_enter_3778_, lean_object* v_p_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3778_, v_p_3779_, v_a_3780_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0___boxed(lean_object* v_enter_3783_, lean_object* v_p_3784_, lean_object* v_as_3785_, lean_object* v_sz_3786_, lean_object* v_i_3787_, lean_object* v_b_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
size_t v_sz_boxed_3791_; size_t v_i_boxed_3792_; lean_object* v_res_3793_; 
v_sz_boxed_3791_ = lean_unbox_usize(v_sz_3786_);
lean_dec(v_sz_3786_);
v_i_boxed_3792_ = lean_unbox_usize(v_i_3787_);
lean_dec(v_i_3787_);
v_res_3793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_3783_, v_p_3784_, v_as_3785_, v_sz_boxed_3791_, v_i_boxed_3792_, v_b_3788_, v___y_3789_);
lean_dec_ref(v_as_3785_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object* v_p_3794_, lean_object* v_enter_3795_){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_3798_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3795_, v_p_3794_, v___x_3797_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3807_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3801_ = v___x_3798_;
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3798_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3807_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v_snd_3803_; lean_object* v___x_3805_; 
v_snd_3803_ = lean_ctor_get(v_a_3799_, 1);
lean_inc(v_snd_3803_);
lean_dec(v_a_3799_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 0, v_snd_3803_);
v___x_3805_ = v___x_3801_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_snd_3803_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
v_a_3808_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3798_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3798_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir___boxed(lean_object* v_p_3816_, lean_object* v_enter_3817_, lean_object* v_a_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l_System_FilePath_walkDir(v_p_3816_, v_enter_3817_);
return v_res_3819_;
}
}
static lean_object* _init_l_IO_FS_readBinFile___closed__0(void){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = lean_unsigned_to_nat(0u);
v___x_3821_ = lean_mk_empty_byte_array(v___x_3820_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object* v_fname_3822_){
_start:
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_io_metadata(v_fname_3822_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; uint8_t v___x_3826_; lean_object* v___x_3827_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
v___x_3826_ = 0;
v___x_3827_ = lean_io_prim_handle_mk(v_fname_3822_, v___x_3826_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; uint64_t v_byteSize_3829_; size_t v___x_3830_; size_t v___x_3831_; uint8_t v___x_3832_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
lean_inc(v_a_3828_);
lean_dec_ref_known(v___x_3827_, 1);
v_byteSize_3829_ = lean_ctor_get_uint64(v_a_3825_, sizeof(void*)*2);
lean_dec(v_a_3825_);
v___x_3830_ = lean_uint64_to_usize(v_byteSize_3829_);
v___x_3831_ = ((size_t)0ULL);
v___x_3832_ = lean_usize_dec_lt(v___x_3831_, v___x_3830_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = lean_obj_once(&l_IO_FS_readBinFile___closed__0, &l_IO_FS_readBinFile___closed__0_once, _init_l_IO_FS_readBinFile___closed__0);
v___x_3834_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_a_3828_, v___x_3833_);
lean_dec(v_a_3828_);
return v___x_3834_;
}
else
{
lean_object* v___x_3835_; 
v___x_3835_ = lean_io_prim_handle_read(v_a_3828_, v___x_3830_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3837_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref_known(v___x_3835_, 1);
v___x_3837_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_a_3828_, v_a_3836_);
lean_dec(v_a_3828_);
return v___x_3837_;
}
else
{
lean_dec(v_a_3828_);
return v___x_3835_;
}
}
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
lean_dec(v_a_3825_);
v_a_3838_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3827_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3827_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
v_a_3846_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3824_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3824_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object* v_fname_3854_, lean_object* v_a_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_IO_FS_readBinFile(v_fname_3854_);
lean_dec_ref(v_fname_3854_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object* v_fname_3859_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = l_IO_FS_readBinFile(v_fname_3859_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3879_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3864_ = v___x_3861_;
v_isShared_3865_ = v_isSharedCheck_3879_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3861_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3879_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
uint8_t v___x_3866_; 
v___x_3866_ = lean_string_validate_utf8(v_a_3862_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3873_; 
lean_dec(v_a_3862_);
v___x_3867_ = ((lean_object*)(l_IO_FS_readFile___closed__0));
v___x_3868_ = lean_string_append(v___x_3867_, v_fname_3859_);
v___x_3869_ = ((lean_object*)(l_IO_FS_readFile___closed__1));
v___x_3870_ = lean_string_append(v___x_3868_, v___x_3869_);
v___x_3871_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3870_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set_tag(v___x_3864_, 1);
lean_ctor_set(v___x_3864_, 0, v___x_3871_);
v___x_3873_ = v___x_3864_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
else
{
lean_object* v___x_3875_; lean_object* v___x_3877_; 
v___x_3875_ = lean_string_from_utf8_unchecked(v_a_3862_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v___x_3875_);
v___x_3877_ = v___x_3864_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3875_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
v_a_3880_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3861_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3861_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object* v_fname_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_IO_FS_readFile(v_fname_3888_);
lean_dec_ref(v_fname_3888_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0(lean_object* v_x_3891_){
_start:
{
lean_object* v_fst_3892_; 
v_fst_3892_ = lean_ctor_get(v_x_3891_, 0);
lean_inc(v_fst_3892_);
return v_fst_3892_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0___boxed(lean_object* v_x_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_IO_withStdin___redArg___lam__0(v_x_3893_);
lean_dec_ref(v_x_3893_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1(lean_object* v___x_3895_, lean_object* v_x_3896_){
_start:
{
lean_inc(v___x_3895_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1___boxed(lean_object* v___x_3897_, lean_object* v_x_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_IO_withStdin___redArg___lam__1(v___x_3897_, v_x_3898_);
lean_dec(v_x_3898_);
lean_dec(v___x_3897_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__2(lean_object* v_toFunctor_3900_, lean_object* v_inst_3901_, lean_object* v_inst_3902_, lean_object* v_x_3903_, lean_object* v___f_3904_, lean_object* v_prev_3905_){
_start:
{
lean_object* v_map_3906_; lean_object* v_mapConst_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___f_3912_; lean_object* v_y_3913_; lean_object* v___x_3914_; 
v_map_3906_ = lean_ctor_get(v_toFunctor_3900_, 0);
lean_inc(v_map_3906_);
v_mapConst_3907_ = lean_ctor_get(v_toFunctor_3900_, 1);
lean_inc(v_mapConst_3907_);
lean_dec_ref(v_toFunctor_3900_);
v___x_3908_ = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(v___x_3908_, 0, v_prev_3905_);
v___x_3909_ = lean_apply_2(v_inst_3901_, lean_box(0), v___x_3908_);
v___x_3910_ = lean_box(0);
v___x_3911_ = lean_apply_4(v_mapConst_3907_, lean_box(0), lean_box(0), v___x_3910_, v___x_3909_);
v___f_3912_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3912_, 0, v___x_3911_);
v_y_3913_ = lean_apply_4(v_inst_3902_, lean_box(0), lean_box(0), v_x_3903_, v___f_3912_);
v___x_3914_ = lean_apply_4(v_map_3906_, lean_box(0), lean_box(0), v___f_3904_, v_y_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg(lean_object* v_inst_3916_, lean_object* v_inst_3917_, lean_object* v_inst_3918_, lean_object* v_h_3919_, lean_object* v_x_3920_){
_start:
{
lean_object* v_toApplicative_3921_; lean_object* v_toBind_3922_; lean_object* v_toFunctor_3923_; lean_object* v___f_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___f_3927_; lean_object* v___x_3928_; 
v_toApplicative_3921_ = lean_ctor_get(v_inst_3916_, 0);
lean_inc_ref(v_toApplicative_3921_);
v_toBind_3922_ = lean_ctor_get(v_inst_3916_, 1);
lean_inc(v_toBind_3922_);
lean_dec_ref(v_inst_3916_);
v_toFunctor_3923_ = lean_ctor_get(v_toApplicative_3921_, 0);
lean_inc_ref(v_toFunctor_3923_);
lean_dec_ref(v_toApplicative_3921_);
v___f_3924_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3925_ = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(v___x_3925_, 0, v_h_3919_);
lean_inc(v_inst_3918_);
v___x_3926_ = lean_apply_2(v_inst_3918_, lean_box(0), v___x_3925_);
v___f_3927_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3927_, 0, v_toFunctor_3923_);
lean_closure_set(v___f_3927_, 1, v_inst_3918_);
lean_closure_set(v___f_3927_, 2, v_inst_3917_);
lean_closure_set(v___f_3927_, 3, v_x_3920_);
lean_closure_set(v___f_3927_, 4, v___f_3924_);
v___x_3928_ = lean_apply_4(v_toBind_3922_, lean_box(0), lean_box(0), v___x_3926_, v___f_3927_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object* v_m_3929_, lean_object* v_00_u03b1_3930_, lean_object* v_inst_3931_, lean_object* v_inst_3932_, lean_object* v_inst_3933_, lean_object* v_h_3934_, lean_object* v_x_3935_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l_IO_withStdin___redArg(v_inst_3931_, v_inst_3932_, v_inst_3933_, v_h_3934_, v_x_3935_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg___lam__2(lean_object* v_toFunctor_3937_, lean_object* v_inst_3938_, lean_object* v_inst_3939_, lean_object* v_x_3940_, lean_object* v___f_3941_, lean_object* v_prev_3942_){
_start:
{
lean_object* v_map_3943_; lean_object* v_mapConst_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___f_3949_; lean_object* v_y_3950_; lean_object* v___x_3951_; 
v_map_3943_ = lean_ctor_get(v_toFunctor_3937_, 0);
lean_inc(v_map_3943_);
v_mapConst_3944_ = lean_ctor_get(v_toFunctor_3937_, 1);
lean_inc(v_mapConst_3944_);
lean_dec_ref(v_toFunctor_3937_);
v___x_3945_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_3945_, 0, v_prev_3942_);
v___x_3946_ = lean_apply_2(v_inst_3938_, lean_box(0), v___x_3945_);
v___x_3947_ = lean_box(0);
v___x_3948_ = lean_apply_4(v_mapConst_3944_, lean_box(0), lean_box(0), v___x_3947_, v___x_3946_);
v___f_3949_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3949_, 0, v___x_3948_);
v_y_3950_ = lean_apply_4(v_inst_3939_, lean_box(0), lean_box(0), v_x_3940_, v___f_3949_);
v___x_3951_ = lean_apply_4(v_map_3943_, lean_box(0), lean_box(0), v___f_3941_, v_y_3950_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg(lean_object* v_inst_3952_, lean_object* v_inst_3953_, lean_object* v_inst_3954_, lean_object* v_h_3955_, lean_object* v_x_3956_){
_start:
{
lean_object* v_toApplicative_3957_; lean_object* v_toBind_3958_; lean_object* v_toFunctor_3959_; lean_object* v___f_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___f_3963_; lean_object* v___x_3964_; 
v_toApplicative_3957_ = lean_ctor_get(v_inst_3952_, 0);
lean_inc_ref(v_toApplicative_3957_);
v_toBind_3958_ = lean_ctor_get(v_inst_3952_, 1);
lean_inc(v_toBind_3958_);
lean_dec_ref(v_inst_3952_);
v_toFunctor_3959_ = lean_ctor_get(v_toApplicative_3957_, 0);
lean_inc_ref(v_toFunctor_3959_);
lean_dec_ref(v_toApplicative_3957_);
v___f_3960_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3961_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_3961_, 0, v_h_3955_);
lean_inc(v_inst_3954_);
v___x_3962_ = lean_apply_2(v_inst_3954_, lean_box(0), v___x_3961_);
v___f_3963_ = lean_alloc_closure((void*)(l_IO_withStdout___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3963_, 0, v_toFunctor_3959_);
lean_closure_set(v___f_3963_, 1, v_inst_3954_);
lean_closure_set(v___f_3963_, 2, v_inst_3953_);
lean_closure_set(v___f_3963_, 3, v_x_3956_);
lean_closure_set(v___f_3963_, 4, v___f_3960_);
v___x_3964_ = lean_apply_4(v_toBind_3958_, lean_box(0), lean_box(0), v___x_3962_, v___f_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object* v_m_3965_, lean_object* v_00_u03b1_3966_, lean_object* v_inst_3967_, lean_object* v_inst_3968_, lean_object* v_inst_3969_, lean_object* v_h_3970_, lean_object* v_x_3971_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = l_IO_withStdout___redArg(v_inst_3967_, v_inst_3968_, v_inst_3969_, v_h_3970_, v_x_3971_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg___lam__2(lean_object* v_toFunctor_3973_, lean_object* v_inst_3974_, lean_object* v_inst_3975_, lean_object* v_x_3976_, lean_object* v___f_3977_, lean_object* v_prev_3978_){
_start:
{
lean_object* v_map_3979_; lean_object* v_mapConst_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___f_3985_; lean_object* v_y_3986_; lean_object* v___x_3987_; 
v_map_3979_ = lean_ctor_get(v_toFunctor_3973_, 0);
lean_inc(v_map_3979_);
v_mapConst_3980_ = lean_ctor_get(v_toFunctor_3973_, 1);
lean_inc(v_mapConst_3980_);
lean_dec_ref(v_toFunctor_3973_);
v___x_3981_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_3981_, 0, v_prev_3978_);
v___x_3982_ = lean_apply_2(v_inst_3974_, lean_box(0), v___x_3981_);
v___x_3983_ = lean_box(0);
v___x_3984_ = lean_apply_4(v_mapConst_3980_, lean_box(0), lean_box(0), v___x_3983_, v___x_3982_);
v___f_3985_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3985_, 0, v___x_3984_);
v_y_3986_ = lean_apply_4(v_inst_3975_, lean_box(0), lean_box(0), v_x_3976_, v___f_3985_);
v___x_3987_ = lean_apply_4(v_map_3979_, lean_box(0), lean_box(0), v___f_3977_, v_y_3986_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg(lean_object* v_inst_3988_, lean_object* v_inst_3989_, lean_object* v_inst_3990_, lean_object* v_h_3991_, lean_object* v_x_3992_){
_start:
{
lean_object* v_toApplicative_3993_; lean_object* v_toBind_3994_; lean_object* v_toFunctor_3995_; lean_object* v___f_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___f_3999_; lean_object* v___x_4000_; 
v_toApplicative_3993_ = lean_ctor_get(v_inst_3988_, 0);
lean_inc_ref(v_toApplicative_3993_);
v_toBind_3994_ = lean_ctor_get(v_inst_3988_, 1);
lean_inc(v_toBind_3994_);
lean_dec_ref(v_inst_3988_);
v_toFunctor_3995_ = lean_ctor_get(v_toApplicative_3993_, 0);
lean_inc_ref(v_toFunctor_3995_);
lean_dec_ref(v_toApplicative_3993_);
v___f_3996_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3997_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_3997_, 0, v_h_3991_);
lean_inc(v_inst_3990_);
v___x_3998_ = lean_apply_2(v_inst_3990_, lean_box(0), v___x_3997_);
v___f_3999_ = lean_alloc_closure((void*)(l_IO_withStderr___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3999_, 0, v_toFunctor_3995_);
lean_closure_set(v___f_3999_, 1, v_inst_3990_);
lean_closure_set(v___f_3999_, 2, v_inst_3989_);
lean_closure_set(v___f_3999_, 3, v_x_3992_);
lean_closure_set(v___f_3999_, 4, v___f_3996_);
v___x_4000_ = lean_apply_4(v_toBind_3994_, lean_box(0), lean_box(0), v___x_3998_, v___f_3999_);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object* v_m_4001_, lean_object* v_00_u03b1_4002_, lean_object* v_inst_4003_, lean_object* v_inst_4004_, lean_object* v_inst_4005_, lean_object* v_h_4006_, lean_object* v_x_4007_){
_start:
{
lean_object* v___x_4008_; 
v___x_4008_ = l_IO_withStderr___redArg(v_inst_4003_, v_inst_4004_, v_inst_4005_, v_h_4006_, v_x_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_IO_print___redArg(lean_object* v_inst_4009_, lean_object* v_s_4010_){
_start:
{
lean_object* v___x_4012_; lean_object* v_putStr_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4012_ = lean_get_stdout();
v_putStr_4013_ = lean_ctor_get(v___x_4012_, 4);
lean_inc_ref(v_putStr_4013_);
lean_dec_ref(v___x_4012_);
v___x_4014_ = lean_apply_1(v_inst_4009_, v_s_4010_);
v___x_4015_ = lean_apply_2(v_putStr_4013_, v___x_4014_, lean_box(0));
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_IO_print___redArg___boxed(lean_object* v_inst_4016_, lean_object* v_s_4017_, lean_object* v_a_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_IO_print___redArg(v_inst_4016_, v_s_4017_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_IO_print(lean_object* v_00_u03b1_4020_, lean_object* v_inst_4021_, lean_object* v_s_4022_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_IO_print___redArg(v_inst_4021_, v_s_4022_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_IO_print___boxed(lean_object* v_00_u03b1_4025_, lean_object* v_inst_4026_, lean_object* v_s_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_IO_print(v_00_u03b1_4025_, v_inst_4026_, v_s_4027_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_IO_println___redArg(lean_object* v_inst_4031_, lean_object* v_s_4032_){
_start:
{
lean_object* v___f_4034_; lean_object* v___x_4035_; uint32_t v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___f_4034_ = ((lean_object*)(l_IO_println___redArg___closed__0));
v___x_4035_ = lean_apply_1(v_inst_4031_, v_s_4032_);
v___x_4036_ = 10;
v___x_4037_ = lean_string_push(v___x_4035_, v___x_4036_);
v___x_4038_ = l_IO_print___redArg(v___f_4034_, v___x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_IO_println___redArg___boxed(lean_object* v_inst_4039_, lean_object* v_s_4040_, lean_object* v_a_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_IO_println___redArg(v_inst_4039_, v_s_4040_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l_IO_println(lean_object* v_00_u03b1_4043_, lean_object* v_inst_4044_, lean_object* v_s_4045_){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = l_IO_println___redArg(v_inst_4044_, v_s_4045_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_IO_println___boxed(lean_object* v_00_u03b1_4048_, lean_object* v_inst_4049_, lean_object* v_s_4050_, lean_object* v_a_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_IO_println(v_00_u03b1_4048_, v_inst_4049_, v_s_4050_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg(lean_object* v_inst_4053_, lean_object* v_s_4054_){
_start:
{
lean_object* v___x_4056_; lean_object* v_putStr_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4056_ = lean_get_stderr();
v_putStr_4057_ = lean_ctor_get(v___x_4056_, 4);
lean_inc_ref(v_putStr_4057_);
lean_dec_ref(v___x_4056_);
v___x_4058_ = lean_apply_1(v_inst_4053_, v_s_4054_);
v___x_4059_ = lean_apply_2(v_putStr_4057_, v___x_4058_, lean_box(0));
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg___boxed(lean_object* v_inst_4060_, lean_object* v_s_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_IO_eprint___redArg(v_inst_4060_, v_s_4061_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint(lean_object* v_00_u03b1_4064_, lean_object* v_inst_4065_, lean_object* v_s_4066_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_IO_eprint___redArg(v_inst_4065_, v_s_4066_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___boxed(lean_object* v_00_u03b1_4069_, lean_object* v_inst_4070_, lean_object* v_s_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l_IO_eprint(v_00_u03b1_4069_, v_inst_4070_, v_s_4071_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg(lean_object* v_inst_4074_, lean_object* v_s_4075_){
_start:
{
lean_object* v___f_4077_; lean_object* v___x_4078_; uint32_t v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___f_4077_ = ((lean_object*)(l_IO_println___redArg___closed__0));
v___x_4078_ = lean_apply_1(v_inst_4074_, v_s_4075_);
v___x_4079_ = 10;
v___x_4080_ = lean_string_push(v___x_4078_, v___x_4079_);
v___x_4081_ = l_IO_eprint___redArg(v___f_4077_, v___x_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg___boxed(lean_object* v_inst_4082_, lean_object* v_s_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l_IO_eprintln___redArg(v_inst_4082_, v_s_4083_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object* v_00_u03b1_4086_, lean_object* v_inst_4087_, lean_object* v_s_4088_){
_start:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_IO_eprintln___redArg(v_inst_4087_, v_s_4088_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___boxed(lean_object* v_00_u03b1_4091_, lean_object* v_inst_4092_, lean_object* v_s_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l_IO_eprintln(v_00_u03b1_4091_, v_inst_4092_, v_s_4093_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object* v_s_4096_){
_start:
{
lean_object* v___x_4098_; lean_object* v_putStr_4099_; lean_object* v___x_4100_; 
v___x_4098_ = lean_get_stderr();
v_putStr_4099_ = lean_ctor_get(v___x_4098_, 4);
lean_inc_ref(v_putStr_4099_);
lean_dec_ref(v___x_4098_);
v___x_4100_ = lean_apply_2(v_putStr_4099_, v_s_4096_, lean_box(0));
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0___boxed(lean_object* v_s_4101_, lean_object* v_a_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_4101_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* lean_io_eprint(lean_object* v_s_4104_){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_4104_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintAux___boxed(lean_object* v_s_4107_, lean_object* v_a_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = lean_io_eprint(v_s_4107_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object* v_s_4110_){
_start:
{
uint32_t v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = 10;
v___x_4113_ = lean_string_push(v_s_4110_, v___x_4112_);
v___x_4114_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v___x_4113_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0___boxed(lean_object* v_s_4115_, lean_object* v_a_4116_){
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_4115_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object* v_s_4118_){
_start:
{
lean_object* v___x_4120_; 
v___x_4120_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_4118_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintlnAux___boxed(lean_object* v_s_4121_, lean_object* v_a_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = lean_io_eprintln(v_s_4121_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_IO_appDir(){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = lean_io_app_path();
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4143_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4130_ = v___x_4127_;
v_isShared_4131_ = v_isSharedCheck_4143_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4127_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4143_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4132_; 
lean_inc(v_a_4128_);
v___x_4132_ = l_System_FilePath_parent(v_a_4128_);
if (lean_obj_tag(v___x_4132_) == 1)
{
lean_object* v_val_4133_; lean_object* v___x_4134_; 
lean_del_object(v___x_4130_);
lean_dec(v_a_4128_);
v_val_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_val_4133_);
lean_dec_ref_known(v___x_4132_, 1);
v___x_4134_ = lean_io_realpath(v_val_4133_);
return v___x_4134_;
}
else
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4141_; 
lean_dec(v___x_4132_);
v___x_4135_ = ((lean_object*)(l_IO_appDir___closed__0));
v___x_4136_ = lean_string_append(v___x_4135_, v_a_4128_);
lean_dec(v_a_4128_);
v___x_4137_ = ((lean_object*)(l_IO_appDir___closed__1));
v___x_4138_ = lean_string_append(v___x_4136_, v___x_4137_);
v___x_4139_ = lean_mk_io_user_error(v___x_4138_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set_tag(v___x_4130_, 1);
lean_ctor_set(v___x_4130_, 0, v___x_4139_);
v___x_4141_ = v___x_4130_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4139_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
else
{
return v___x_4127_;
}
}
}
LEAN_EXPORT lean_object* l_IO_appDir___boxed(lean_object* v_a_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_IO_appDir();
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object* v_p_4146_){
_start:
{
uint8_t v___x_4163_; 
v___x_4163_ = l_System_FilePath_isDir(v_p_4146_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; 
lean_inc_ref(v_p_4146_);
v___x_4164_ = l_System_FilePath_parent(v_p_4146_);
if (lean_obj_tag(v___x_4164_) == 1)
{
lean_object* v_val_4165_; lean_object* v___x_4166_; 
v_val_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_val_4165_);
lean_dec_ref_known(v___x_4164_, 1);
v___x_4166_ = l_IO_FS_createDirAll(v_val_4165_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_dec_ref_known(v___x_4166_, 1);
goto v___jp_4148_;
}
else
{
lean_dec_ref(v_p_4146_);
return v___x_4166_;
}
}
else
{
lean_dec(v___x_4164_);
goto v___jp_4148_;
}
}
else
{
lean_object* v___x_4167_; lean_object* v___x_4168_; 
lean_dec_ref(v_p_4146_);
v___x_4167_ = lean_box(0);
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
return v___x_4168_;
}
v___jp_4148_:
{
lean_object* v___x_4149_; 
v___x_4149_ = lean_io_create_dir(v_p_4146_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_dec_ref(v_p_4146_);
return v___x_4149_;
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4162_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4152_ = v___x_4149_;
v_isShared_4153_ = v_isSharedCheck_4162_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4149_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4162_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
uint8_t v___x_4154_; 
v___x_4154_ = l_System_FilePath_isDir(v_p_4146_);
lean_dec_ref(v_p_4146_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4156_; 
if (v_isShared_4153_ == 0)
{
v___x_4156_ = v___x_4152_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_a_4150_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
else
{
lean_object* v___x_4158_; lean_object* v___x_4160_; 
lean_dec(v_a_4150_);
v___x_4158_ = lean_box(0);
if (v_isShared_4153_ == 0)
{
lean_ctor_set_tag(v___x_4152_, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4158_);
v___x_4160_ = v___x_4152_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object* v_p_4169_, lean_object* v_a_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_IO_FS_createDirAll(v_p_4169_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(lean_object* v_as_4172_, size_t v_sz_4173_, size_t v_i_4174_, lean_object* v_b_4175_){
_start:
{
lean_object* v_a_4178_; uint8_t v___x_4182_; 
v___x_4182_ = lean_usize_dec_lt(v_i_4174_, v_sz_4173_);
if (v___x_4182_ == 0)
{
lean_object* v___x_4183_; 
v___x_4183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4183_, 0, v_b_4175_);
return v___x_4183_;
}
else
{
lean_object* v_a_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v_a_4184_ = lean_array_uget_borrowed(v_as_4172_, v_i_4174_);
lean_inc(v_a_4184_);
v___x_4185_ = l_IO_FS_DirEntry_path(v_a_4184_);
v___x_4186_ = lean_io_symlink_metadata(v___x_4185_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; uint8_t v_type_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; uint8_t v___x_4191_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4187_);
lean_dec_ref_known(v___x_4186_, 1);
v_type_4188_ = lean_ctor_get_uint8(v_a_4187_, sizeof(void*)*2 + 16);
lean_dec(v_a_4187_);
v___x_4189_ = lean_box(0);
v___x_4190_ = 0;
v___x_4191_ = l_IO_FS_instBEqFileType_beq(v_type_4188_, v___x_4190_);
if (v___x_4191_ == 0)
{
lean_object* v___x_4192_; 
v___x_4192_ = lean_io_remove_file(v___x_4185_);
lean_dec_ref(v___x_4185_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_dec_ref_known(v___x_4192_, 1);
v_a_4178_ = v___x_4189_;
goto v___jp_4177_;
}
else
{
return v___x_4192_;
}
}
else
{
lean_object* v___x_4193_; 
v___x_4193_ = l_IO_FS_removeDirAll(v___x_4185_);
lean_dec_ref(v___x_4185_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_dec_ref_known(v___x_4193_, 1);
v_a_4178_ = v___x_4189_;
goto v___jp_4177_;
}
else
{
return v___x_4193_;
}
}
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec_ref(v___x_4185_);
v_a_4194_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4186_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4186_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
v___jp_4177_:
{
size_t v___x_4179_; size_t v___x_4180_; 
v___x_4179_ = ((size_t)1ULL);
v___x_4180_ = lean_usize_add(v_i_4174_, v___x_4179_);
v_i_4174_ = v___x_4180_;
v_b_4175_ = v_a_4178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object* v_p_4202_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = lean_io_read_dir(v_p_4202_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4206_; size_t v_sz_4207_; size_t v___x_4208_; lean_object* v___x_4209_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4205_);
lean_dec_ref_known(v___x_4204_, 1);
v___x_4206_ = lean_box(0);
v_sz_4207_ = lean_array_size(v_a_4205_);
v___x_4208_ = ((size_t)0ULL);
v___x_4209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_a_4205_, v_sz_4207_, v___x_4208_, v___x_4206_);
lean_dec(v_a_4205_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v___x_4210_; 
lean_dec_ref_known(v___x_4209_, 1);
v___x_4210_ = lean_io_remove_dir(v_p_4202_);
return v___x_4210_;
}
else
{
return v___x_4209_;
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
v_a_4211_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4204_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4204_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object* v_p_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_IO_FS_removeDirAll(v_p_4219_);
lean_dec_ref(v_p_4219_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0___boxed(lean_object* v_as_4222_, lean_object* v_sz_4223_, lean_object* v_i_4224_, lean_object* v_b_4225_, lean_object* v___y_4226_){
_start:
{
size_t v_sz_boxed_4227_; size_t v_i_boxed_4228_; lean_object* v_res_4229_; 
v_sz_boxed_4227_ = lean_unbox_usize(v_sz_4223_);
lean_dec(v_sz_4223_);
v_i_boxed_4228_ = lean_unbox_usize(v_i_4224_);
lean_dec(v_i_4224_);
v_res_4229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_as_4222_, v_sz_boxed_4227_, v_i_boxed_4228_, v_b_4225_);
lean_dec_ref(v_as_4222_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg___lam__2(lean_object* v_toFunctor_4230_, lean_object* v_f_4231_, lean_object* v_inst_4232_, lean_object* v_inst_4233_, lean_object* v___f_4234_, lean_object* v_____x_4235_){
_start:
{
lean_object* v_fst_4236_; lean_object* v_snd_4237_; lean_object* v_map_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___f_4242_; lean_object* v_y_4243_; lean_object* v___x_4244_; 
v_fst_4236_ = lean_ctor_get(v_____x_4235_, 0);
lean_inc(v_fst_4236_);
v_snd_4237_ = lean_ctor_get(v_____x_4235_, 1);
lean_inc_n(v_snd_4237_, 2);
lean_dec_ref(v_____x_4235_);
v_map_4238_ = lean_ctor_get(v_toFunctor_4230_, 0);
lean_inc(v_map_4238_);
lean_dec_ref(v_toFunctor_4230_);
v___x_4239_ = lean_apply_2(v_f_4231_, v_fst_4236_, v_snd_4237_);
v___x_4240_ = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(v___x_4240_, 0, v_snd_4237_);
v___x_4241_ = lean_apply_2(v_inst_4232_, lean_box(0), v___x_4240_);
v___f_4242_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4242_, 0, v___x_4241_);
v_y_4243_ = lean_apply_4(v_inst_4233_, lean_box(0), lean_box(0), v___x_4239_, v___f_4242_);
v___x_4244_ = lean_apply_4(v_map_4238_, lean_box(0), lean_box(0), v___f_4234_, v_y_4243_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg(lean_object* v_inst_4246_, lean_object* v_inst_4247_, lean_object* v_inst_4248_, lean_object* v_f_4249_){
_start:
{
lean_object* v_toApplicative_4250_; lean_object* v_toBind_4251_; lean_object* v_toFunctor_4252_; lean_object* v___f_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___f_4256_; lean_object* v___x_4257_; 
v_toApplicative_4250_ = lean_ctor_get(v_inst_4246_, 0);
lean_inc_ref(v_toApplicative_4250_);
v_toBind_4251_ = lean_ctor_get(v_inst_4246_, 1);
lean_inc(v_toBind_4251_);
lean_dec_ref(v_inst_4246_);
v_toFunctor_4252_ = lean_ctor_get(v_toApplicative_4250_, 0);
lean_inc_ref(v_toFunctor_4252_);
lean_dec_ref(v_toApplicative_4250_);
v___f_4253_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4254_ = ((lean_object*)(l_IO_FS_withTempFile___redArg___closed__0));
lean_inc(v_inst_4248_);
v___x_4255_ = lean_apply_2(v_inst_4248_, lean_box(0), v___x_4254_);
v___f_4256_ = lean_alloc_closure((void*)(l_IO_FS_withTempFile___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4256_, 0, v_toFunctor_4252_);
lean_closure_set(v___f_4256_, 1, v_f_4249_);
lean_closure_set(v___f_4256_, 2, v_inst_4248_);
lean_closure_set(v___f_4256_, 3, v_inst_4247_);
lean_closure_set(v___f_4256_, 4, v___f_4253_);
v___x_4257_ = lean_apply_4(v_toBind_4251_, lean_box(0), lean_box(0), v___x_4255_, v___f_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile(lean_object* v_m_4258_, lean_object* v_00_u03b1_4259_, lean_object* v_inst_4260_, lean_object* v_inst_4261_, lean_object* v_inst_4262_, lean_object* v_f_4263_){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_IO_FS_withTempFile___redArg(v_inst_4260_, v_inst_4261_, v_inst_4262_, v_f_4263_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg___lam__2(lean_object* v_toFunctor_4265_, lean_object* v_f_4266_, lean_object* v_inst_4267_, lean_object* v_inst_4268_, lean_object* v___f_4269_, lean_object* v_path_4270_){
_start:
{
lean_object* v_map_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___f_4275_; lean_object* v_y_4276_; lean_object* v___x_4277_; 
v_map_4271_ = lean_ctor_get(v_toFunctor_4265_, 0);
lean_inc(v_map_4271_);
lean_dec_ref(v_toFunctor_4265_);
lean_inc_ref(v_path_4270_);
v___x_4272_ = lean_apply_1(v_f_4266_, v_path_4270_);
v___x_4273_ = lean_alloc_closure((void*)(l_IO_FS_removeDirAll___boxed), 2, 1);
lean_closure_set(v___x_4273_, 0, v_path_4270_);
v___x_4274_ = lean_apply_2(v_inst_4267_, lean_box(0), v___x_4273_);
v___f_4275_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4275_, 0, v___x_4274_);
v_y_4276_ = lean_apply_4(v_inst_4268_, lean_box(0), lean_box(0), v___x_4272_, v___f_4275_);
v___x_4277_ = lean_apply_4(v_map_4271_, lean_box(0), lean_box(0), v___f_4269_, v_y_4276_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg(lean_object* v_inst_4279_, lean_object* v_inst_4280_, lean_object* v_inst_4281_, lean_object* v_f_4282_){
_start:
{
lean_object* v_toApplicative_4283_; lean_object* v_toBind_4284_; lean_object* v_toFunctor_4285_; lean_object* v___f_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___f_4289_; lean_object* v___x_4290_; 
v_toApplicative_4283_ = lean_ctor_get(v_inst_4279_, 0);
lean_inc_ref(v_toApplicative_4283_);
v_toBind_4284_ = lean_ctor_get(v_inst_4279_, 1);
lean_inc(v_toBind_4284_);
lean_dec_ref(v_inst_4279_);
v_toFunctor_4285_ = lean_ctor_get(v_toApplicative_4283_, 0);
lean_inc_ref(v_toFunctor_4285_);
lean_dec_ref(v_toApplicative_4283_);
v___f_4286_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4287_ = ((lean_object*)(l_IO_FS_withTempDir___redArg___closed__0));
lean_inc(v_inst_4281_);
v___x_4288_ = lean_apply_2(v_inst_4281_, lean_box(0), v___x_4287_);
v___f_4289_ = lean_alloc_closure((void*)(l_IO_FS_withTempDir___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4289_, 0, v_toFunctor_4285_);
lean_closure_set(v___f_4289_, 1, v_f_4282_);
lean_closure_set(v___f_4289_, 2, v_inst_4281_);
lean_closure_set(v___f_4289_, 3, v_inst_4280_);
lean_closure_set(v___f_4289_, 4, v___f_4286_);
v___x_4290_ = lean_apply_4(v_toBind_4284_, lean_box(0), lean_box(0), v___x_4288_, v___f_4289_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir(lean_object* v_m_4291_, lean_object* v_00_u03b1_4292_, lean_object* v_inst_4293_, lean_object* v_inst_4294_, lean_object* v_inst_4295_, lean_object* v_f_4296_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l_IO_FS_withTempDir___redArg(v_inst_4293_, v_inst_4294_, v_inst_4295_, v_f_4296_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_getCurrentDir___boxed(lean_object* v_a_00___x40___internal___hyg_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = lean_io_process_get_current_dir();
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_setCurrentDir___boxed(lean_object* v_path_4303_, lean_object* v_a_00___x40___internal___hyg_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = lean_io_process_set_current_dir(v_path_4303_);
lean_dec_ref(v_path_4303_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_getPID___boxed(lean_object* v_a_00___x40___internal___hyg_4307_){
_start:
{
uint32_t v_res_4308_; lean_object* v_r_4309_; 
v_res_4308_ = lean_io_process_get_pid();
v_r_4309_ = lean_box_uint32(v_res_4308_);
return v_r_4309_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx(uint8_t v_x_4310_){
_start:
{
switch(v_x_4310_)
{
case 0:
{
lean_object* v___x_4311_; 
v___x_4311_ = lean_unsigned_to_nat(0u);
return v___x_4311_;
}
case 1:
{
lean_object* v___x_4312_; 
v___x_4312_ = lean_unsigned_to_nat(1u);
return v___x_4312_;
}
default: 
{
lean_object* v___x_4313_; 
v___x_4313_ = lean_unsigned_to_nat(2u);
return v___x_4313_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx___boxed(lean_object* v_x_4314_){
_start:
{
uint8_t v_x_boxed_4315_; lean_object* v_res_4316_; 
v_x_boxed_4315_ = lean_unbox(v_x_4314_);
v_res_4316_ = l_IO_Process_Stdio_ctorIdx(v_x_boxed_4315_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg(lean_object* v_k_4317_){
_start:
{
lean_inc(v_k_4317_);
return v_k_4317_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg___boxed(lean_object* v_k_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l_IO_Process_Stdio_ctorElim___redArg(v_k_4318_);
lean_dec(v_k_4318_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim(lean_object* v_motive_4320_, lean_object* v_ctorIdx_4321_, uint8_t v_t_4322_, lean_object* v_h_4323_, lean_object* v_k_4324_){
_start:
{
lean_inc(v_k_4324_);
return v_k_4324_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___boxed(lean_object* v_motive_4325_, lean_object* v_ctorIdx_4326_, lean_object* v_t_4327_, lean_object* v_h_4328_, lean_object* v_k_4329_){
_start:
{
uint8_t v_t_boxed_4330_; lean_object* v_res_4331_; 
v_t_boxed_4330_ = lean_unbox(v_t_4327_);
v_res_4331_ = l_IO_Process_Stdio_ctorElim(v_motive_4325_, v_ctorIdx_4326_, v_t_boxed_4330_, v_h_4328_, v_k_4329_);
lean_dec(v_k_4329_);
lean_dec(v_ctorIdx_4326_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg(lean_object* v_piped_4332_){
_start:
{
lean_inc(v_piped_4332_);
return v_piped_4332_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg___boxed(lean_object* v_piped_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = l_IO_Process_Stdio_piped_elim___redArg(v_piped_4333_);
lean_dec(v_piped_4333_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim(lean_object* v_motive_4335_, uint8_t v_t_4336_, lean_object* v_h_4337_, lean_object* v_piped_4338_){
_start:
{
lean_inc(v_piped_4338_);
return v_piped_4338_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___boxed(lean_object* v_motive_4339_, lean_object* v_t_4340_, lean_object* v_h_4341_, lean_object* v_piped_4342_){
_start:
{
uint8_t v_t_boxed_4343_; lean_object* v_res_4344_; 
v_t_boxed_4343_ = lean_unbox(v_t_4340_);
v_res_4344_ = l_IO_Process_Stdio_piped_elim(v_motive_4339_, v_t_boxed_4343_, v_h_4341_, v_piped_4342_);
lean_dec(v_piped_4342_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg(lean_object* v_inherit_4345_){
_start:
{
lean_inc(v_inherit_4345_);
return v_inherit_4345_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg___boxed(lean_object* v_inherit_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l_IO_Process_Stdio_inherit_elim___redArg(v_inherit_4346_);
lean_dec(v_inherit_4346_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim(lean_object* v_motive_4348_, uint8_t v_t_4349_, lean_object* v_h_4350_, lean_object* v_inherit_4351_){
_start:
{
lean_inc(v_inherit_4351_);
return v_inherit_4351_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___boxed(lean_object* v_motive_4352_, lean_object* v_t_4353_, lean_object* v_h_4354_, lean_object* v_inherit_4355_){
_start:
{
uint8_t v_t_boxed_4356_; lean_object* v_res_4357_; 
v_t_boxed_4356_ = lean_unbox(v_t_4353_);
v_res_4357_ = l_IO_Process_Stdio_inherit_elim(v_motive_4352_, v_t_boxed_4356_, v_h_4354_, v_inherit_4355_);
lean_dec(v_inherit_4355_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg(lean_object* v_null_4358_){
_start:
{
lean_inc(v_null_4358_);
return v_null_4358_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg___boxed(lean_object* v_null_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l_IO_Process_Stdio_null_elim___redArg(v_null_4359_);
lean_dec(v_null_4359_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim(lean_object* v_motive_4361_, uint8_t v_t_4362_, lean_object* v_h_4363_, lean_object* v_null_4364_){
_start:
{
lean_inc(v_null_4364_);
return v_null_4364_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___boxed(lean_object* v_motive_4365_, lean_object* v_t_4366_, lean_object* v_h_4367_, lean_object* v_null_4368_){
_start:
{
uint8_t v_t_boxed_4369_; lean_object* v_res_4370_; 
v_t_boxed_4369_ = lean_unbox(v_t_4366_);
v_res_4370_ = l_IO_Process_Stdio_null_elim(v_motive_4365_, v_t_boxed_4369_, v_h_4367_, v_null_4368_);
lean_dec(v_null_4368_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object* v_args_4373_, lean_object* v_a_00___x40___internal___hyg_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = lean_io_process_spawn(v_args_4373_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object* v_cfg_4379_, lean_object* v_a_00___x40___internal___hyg_4380_, lean_object* v_a_00___x40___internal___hyg_4381_){
_start:
{
lean_object* v_res_4382_; 
v_res_4382_ = lean_io_process_child_wait(v_cfg_4379_, v_a_00___x40___internal___hyg_4380_);
lean_dec_ref(v_a_00___x40___internal___hyg_4380_);
lean_dec_ref(v_cfg_4379_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_tryWait___boxed(lean_object* v_cfg_4386_, lean_object* v_a_00___x40___internal___hyg_4387_, lean_object* v_a_00___x40___internal___hyg_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = lean_io_process_child_try_wait(v_cfg_4386_, v_a_00___x40___internal___hyg_4387_);
lean_dec_ref(v_a_00___x40___internal___hyg_4387_);
lean_dec_ref(v_cfg_4386_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_kill___boxed(lean_object* v_cfg_4393_, lean_object* v_a_00___x40___internal___hyg_4394_, lean_object* v_a_00___x40___internal___hyg_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = lean_io_process_child_kill(v_cfg_4393_, v_a_00___x40___internal___hyg_4394_);
lean_dec_ref(v_a_00___x40___internal___hyg_4394_);
lean_dec_ref(v_cfg_4393_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object* v_cfg_4400_, lean_object* v_a_00___x40___internal___hyg_4401_, lean_object* v_a_00___x40___internal___hyg_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = lean_io_process_child_take_stdin(v_cfg_4400_, v_a_00___x40___internal___hyg_4401_);
lean_dec_ref(v_cfg_4400_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_pid___boxed(lean_object* v_cfg_4406_, lean_object* v_a_00___x40___internal___hyg_4407_){
_start:
{
uint32_t v_res_4408_; lean_object* v_r_4409_; 
v_res_4408_ = lean_io_process_child_pid(v_cfg_4406_, v_a_00___x40___internal___hyg_4407_);
lean_dec_ref(v_cfg_4406_);
v_r_4409_ = lean_box_uint32(v_res_4408_);
return v_r_4409_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(lean_object* v_e_4410_){
_start:
{
if (lean_obj_tag(v_e_4410_) == 0)
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4421_; 
v_a_4412_ = lean_ctor_get(v_e_4410_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_e_4410_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4414_ = v_e_4410_;
v_isShared_4415_ = v_isSharedCheck_4421_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v_e_4410_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4421_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4419_; 
v___x_4416_ = lean_io_error_to_string(v_a_4412_);
v___x_4417_ = lean_mk_io_user_error(v___x_4416_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set_tag(v___x_4414_, 1);
lean_ctor_set(v___x_4414_, 0, v___x_4417_);
v___x_4419_ = v___x_4414_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4417_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
v_a_4422_ = lean_ctor_get(v_e_4410_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v_e_4410_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v_e_4410_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v_e_4410_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
lean_ctor_set_tag(v___x_4424_, 0);
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_a_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg___boxed(lean_object* v_e_4430_, lean_object* v_a_4431_){
_start:
{
lean_object* v_res_4432_; 
v_res_4432_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_4430_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0(lean_object* v_00_u03b1_4433_, lean_object* v_e_4434_){
_start:
{
lean_object* v___x_4436_; 
v___x_4436_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_4434_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___boxed(lean_object* v_00_u03b1_4437_, lean_object* v_e_4438_, lean_object* v_a_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l_IO_ofExcept___at___00IO_Process_output_spec__0(v_00_u03b1_4437_, v_e_4438_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0(lean_object* v_stdout_4441_){
_start:
{
lean_object* v___x_4443_; 
v___x_4443_ = l_IO_FS_Handle_readToEnd(v_stdout_4441_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
v_a_4444_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4443_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4443_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
lean_ctor_set_tag(v___x_4446_, 1);
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
v_a_4452_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4443_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4443_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
lean_ctor_set_tag(v___x_4454_, 0);
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0___boxed(lean_object* v_stdout_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_IO_Process_output___lam__0(v_stdout_4460_);
lean_dec(v_stdout_4460_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object* v_args_4468_, lean_object* v_input_x3f_4469_){
_start:
{
lean_object* v_child_4472_; 
if (lean_obj_tag(v_input_x3f_4469_) == 1)
{
lean_object* v_val_4519_; lean_object* v___x_4520_; lean_object* v_cmd_4521_; lean_object* v_args_4522_; lean_object* v_cwd_4523_; lean_object* v_env_4524_; uint8_t v_inheritEnv_4525_; uint8_t v_setsid_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4573_; 
v_val_4519_ = lean_ctor_get(v_input_x3f_4469_, 0);
v___x_4520_ = ((lean_object*)(l_IO_Process_output___closed__1));
v_cmd_4521_ = lean_ctor_get(v_args_4468_, 1);
v_args_4522_ = lean_ctor_get(v_args_4468_, 2);
v_cwd_4523_ = lean_ctor_get(v_args_4468_, 3);
v_env_4524_ = lean_ctor_get(v_args_4468_, 4);
v_inheritEnv_4525_ = lean_ctor_get_uint8(v_args_4468_, sizeof(void*)*5);
v_setsid_4526_ = lean_ctor_get_uint8(v_args_4468_, sizeof(void*)*5 + 1);
v_isSharedCheck_4573_ = !lean_is_exclusive(v_args_4468_);
if (v_isSharedCheck_4573_ == 0)
{
lean_object* v_unused_4574_; 
v_unused_4574_ = lean_ctor_get(v_args_4468_, 0);
lean_dec(v_unused_4574_);
v___x_4528_ = v_args_4468_;
v_isShared_4529_ = v_isSharedCheck_4573_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_env_4524_);
lean_inc(v_cwd_4523_);
lean_inc(v_args_4522_);
lean_inc(v_cmd_4521_);
lean_dec(v_args_4468_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4573_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 0, v___x_4520_);
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4520_);
lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_cmd_4521_);
lean_ctor_set(v_reuseFailAlloc_4572_, 2, v_args_4522_);
lean_ctor_set(v_reuseFailAlloc_4572_, 3, v_cwd_4523_);
lean_ctor_set(v_reuseFailAlloc_4572_, 4, v_env_4524_);
lean_ctor_set_uint8(v_reuseFailAlloc_4572_, sizeof(void*)*5, v_inheritEnv_4525_);
lean_ctor_set_uint8(v_reuseFailAlloc_4572_, sizeof(void*)*5 + 1, v_setsid_4526_);
v___x_4531_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
lean_object* v___x_4532_; 
v___x_4532_ = lean_io_process_spawn(v___x_4531_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; lean_object* v___x_4534_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_a_4533_);
lean_dec_ref_known(v___x_4532_, 1);
v___x_4534_ = lean_io_process_child_take_stdin(v___x_4520_, v_a_4533_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v_a_4535_; lean_object* v_fst_4536_; lean_object* v_snd_4537_; lean_object* v___x_4538_; 
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
lean_inc(v_a_4535_);
lean_dec_ref_known(v___x_4534_, 1);
v_fst_4536_ = lean_ctor_get(v_a_4535_, 0);
lean_inc(v_fst_4536_);
v_snd_4537_ = lean_ctor_get(v_a_4535_, 1);
lean_inc(v_snd_4537_);
lean_dec(v_a_4535_);
v___x_4538_ = lean_io_prim_handle_put_str(v_fst_4536_, v_val_4519_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_object* v___x_4539_; 
lean_dec_ref_known(v___x_4538_, 1);
v___x_4539_ = lean_io_prim_handle_flush(v_fst_4536_);
lean_dec(v_fst_4536_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_dec_ref_known(v___x_4539_, 1);
v_child_4472_ = v_snd_4537_;
goto v___jp_4471_;
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
lean_dec(v_snd_4537_);
v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4539_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4539_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
}
else
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4555_; 
lean_dec(v_snd_4537_);
lean_dec(v_fst_4536_);
v_a_4548_ = lean_ctor_get(v___x_4538_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4550_ = v___x_4538_;
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___x_4538_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4553_; 
if (v_isShared_4551_ == 0)
{
v___x_4553_ = v___x_4550_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_a_4548_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
v_a_4556_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4534_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4534_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
else
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4571_; 
v_a_4564_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4566_ = v___x_4532_;
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4532_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4569_; 
if (v_isShared_4567_ == 0)
{
v___x_4569_ = v___x_4566_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
}
}
else
{
lean_object* v___x_4575_; lean_object* v_cmd_4576_; lean_object* v_args_4577_; lean_object* v_cwd_4578_; lean_object* v_env_4579_; uint8_t v_inheritEnv_4580_; uint8_t v_setsid_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4598_; 
v___x_4575_ = ((lean_object*)(l_IO_Process_output___closed__0));
v_cmd_4576_ = lean_ctor_get(v_args_4468_, 1);
v_args_4577_ = lean_ctor_get(v_args_4468_, 2);
v_cwd_4578_ = lean_ctor_get(v_args_4468_, 3);
v_env_4579_ = lean_ctor_get(v_args_4468_, 4);
v_inheritEnv_4580_ = lean_ctor_get_uint8(v_args_4468_, sizeof(void*)*5);
v_setsid_4581_ = lean_ctor_get_uint8(v_args_4468_, sizeof(void*)*5 + 1);
v_isSharedCheck_4598_ = !lean_is_exclusive(v_args_4468_);
if (v_isSharedCheck_4598_ == 0)
{
lean_object* v_unused_4599_; 
v_unused_4599_ = lean_ctor_get(v_args_4468_, 0);
lean_dec(v_unused_4599_);
v___x_4583_ = v_args_4468_;
v_isShared_4584_ = v_isSharedCheck_4598_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_env_4579_);
lean_inc(v_cwd_4578_);
lean_inc(v_args_4577_);
lean_inc(v_cmd_4576_);
lean_dec(v_args_4468_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4598_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4586_; 
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4575_);
v___x_4586_ = v___x_4583_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4575_);
lean_ctor_set(v_reuseFailAlloc_4597_, 1, v_cmd_4576_);
lean_ctor_set(v_reuseFailAlloc_4597_, 2, v_args_4577_);
lean_ctor_set(v_reuseFailAlloc_4597_, 3, v_cwd_4578_);
lean_ctor_set(v_reuseFailAlloc_4597_, 4, v_env_4579_);
lean_ctor_set_uint8(v_reuseFailAlloc_4597_, sizeof(void*)*5, v_inheritEnv_4580_);
lean_ctor_set_uint8(v_reuseFailAlloc_4597_, sizeof(void*)*5 + 1, v_setsid_4581_);
v___x_4586_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
lean_object* v___x_4587_; 
v___x_4587_ = lean_io_process_spawn(v___x_4586_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; 
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
lean_inc(v_a_4588_);
lean_dec_ref_known(v___x_4587_, 1);
v_child_4472_ = v_a_4588_;
goto v___jp_4471_;
}
else
{
lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4596_; 
v_a_4589_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4591_ = v___x_4587_;
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___x_4587_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4594_; 
if (v_isShared_4592_ == 0)
{
v___x_4594_ = v___x_4591_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_a_4589_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
}
}
v___jp_4471_:
{
lean_object* v_stdout_4473_; lean_object* v_stderr_4474_; lean_object* v___f_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; 
v_stdout_4473_ = lean_ctor_get(v_child_4472_, 1);
v_stderr_4474_ = lean_ctor_get(v_child_4472_, 2);
lean_inc(v_stdout_4473_);
v___f_4475_ = lean_alloc_closure((void*)(l_IO_Process_output___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4475_, 0, v_stdout_4473_);
v___x_4476_ = lean_unsigned_to_nat(9u);
v___x_4477_ = lean_io_as_task(v___f_4475_, v___x_4476_);
v___x_4478_ = l_IO_FS_Handle_readToEnd(v_stderr_4474_);
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_object* v_a_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v_a_4479_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4479_);
lean_dec_ref_known(v___x_4478_, 1);
v___x_4480_ = ((lean_object*)(l_IO_Process_output___closed__0));
v___x_4481_ = lean_io_process_child_wait(v___x_4480_, v_child_4472_);
lean_dec_ref(v_child_4472_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref_known(v___x_4481_, 1);
v___x_4483_ = lean_task_get_own(v___x_4477_);
v___x_4484_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v___x_4483_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4494_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4487_ = v___x_4484_;
v_isShared_4488_ = v_isSharedCheck_4494_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4484_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4494_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4489_; uint32_t v___x_4490_; lean_object* v___x_4492_; 
v___x_4489_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4489_, 0, v_a_4485_);
lean_ctor_set(v___x_4489_, 1, v_a_4479_);
v___x_4490_ = lean_unbox_uint32(v_a_4482_);
lean_dec(v_a_4482_);
lean_ctor_set_uint32(v___x_4489_, sizeof(void*)*2, v___x_4490_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 0, v___x_4489_);
v___x_4492_ = v___x_4487_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4489_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
lean_dec(v_a_4482_);
lean_dec(v_a_4479_);
v_a_4495_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4484_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4484_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
else
{
lean_object* v_a_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4510_; 
lean_dec(v_a_4479_);
lean_dec_ref(v___x_4477_);
v_a_4503_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4505_ = v___x_4481_;
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_a_4503_);
lean_dec(v___x_4481_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4510_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4508_; 
if (v_isShared_4506_ == 0)
{
v___x_4508_ = v___x_4505_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4503_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
}
}
}
}
else
{
lean_object* v_a_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4518_; 
lean_dec_ref(v___x_4477_);
lean_dec_ref(v_child_4472_);
v_a_4511_ = lean_ctor_get(v___x_4478_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4513_ = v___x_4478_;
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_a_4511_);
lean_dec(v___x_4478_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4516_; 
if (v_isShared_4514_ == 0)
{
v___x_4516_ = v___x_4513_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_a_4511_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___boxed(lean_object* v_args_4600_, lean_object* v_input_x3f_4601_, lean_object* v_a_4602_){
_start:
{
lean_object* v_res_4603_; 
v_res_4603_ = l_IO_Process_output(v_args_4600_, v_input_x3f_4601_);
lean_dec(v_input_x3f_4601_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_run(lean_object* v_args_4607_, lean_object* v_input_x3f_4608_){
_start:
{
lean_object* v___x_4610_; 
lean_inc_ref(v_args_4607_);
v___x_4610_ = l_IO_Process_output(v_args_4607_, v_input_x3f_4608_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4638_; 
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4613_ = v___x_4610_;
v_isShared_4614_ = v_isSharedCheck_4638_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4610_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4638_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
uint32_t v_exitCode_4615_; lean_object* v_stdout_4616_; lean_object* v_stderr_4617_; uint32_t v___x_4618_; uint8_t v___x_4619_; 
v_exitCode_4615_ = lean_ctor_get_uint32(v_a_4611_, sizeof(void*)*2);
v_stdout_4616_ = lean_ctor_get(v_a_4611_, 0);
lean_inc_ref(v_stdout_4616_);
v_stderr_4617_ = lean_ctor_get(v_a_4611_, 1);
lean_inc_ref(v_stderr_4617_);
lean_dec(v_a_4611_);
v___x_4618_ = 0;
v___x_4619_ = lean_uint32_dec_eq(v_exitCode_4615_, v___x_4618_);
if (v___x_4619_ == 0)
{
lean_object* v_cmd_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4633_; 
lean_dec_ref(v_stdout_4616_);
v_cmd_4620_ = lean_ctor_get(v_args_4607_, 1);
lean_inc_ref(v_cmd_4620_);
lean_dec_ref(v_args_4607_);
v___x_4621_ = ((lean_object*)(l_IO_Process_run___closed__0));
v___x_4622_ = lean_string_append(v___x_4621_, v_cmd_4620_);
lean_dec_ref(v_cmd_4620_);
v___x_4623_ = ((lean_object*)(l_IO_Process_run___closed__1));
v___x_4624_ = lean_string_append(v___x_4622_, v___x_4623_);
v___x_4625_ = lean_uint32_to_nat(v_exitCode_4615_);
v___x_4626_ = l_Nat_reprFast(v___x_4625_);
v___x_4627_ = lean_string_append(v___x_4624_, v___x_4626_);
lean_dec_ref(v___x_4626_);
v___x_4628_ = ((lean_object*)(l_IO_Process_run___closed__2));
v___x_4629_ = lean_string_append(v___x_4627_, v___x_4628_);
v___x_4630_ = lean_string_append(v___x_4629_, v_stderr_4617_);
lean_dec_ref(v_stderr_4617_);
v___x_4631_ = lean_mk_io_user_error(v___x_4630_);
if (v_isShared_4614_ == 0)
{
lean_ctor_set_tag(v___x_4613_, 1);
lean_ctor_set(v___x_4613_, 0, v___x_4631_);
v___x_4633_ = v___x_4613_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v___x_4631_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
else
{
lean_object* v___x_4636_; 
lean_dec_ref(v_stderr_4617_);
lean_dec_ref(v_args_4607_);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 0, v_stdout_4616_);
v___x_4636_ = v___x_4613_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_stdout_4616_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4646_; 
lean_dec_ref(v_args_4607_);
v_a_4639_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4641_ = v___x_4610_;
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4610_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_run___boxed(lean_object* v_args_4647_, lean_object* v_input_x3f_4648_, lean_object* v_a_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l_IO_Process_run(v_args_4647_, v_input_x3f_4648_);
lean_dec(v_input_x3f_4648_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object* v_00_u03b1_4654_, lean_object* v_a_00___x40___internal___hyg_4655_, lean_object* v_a_00___x40___internal___hyg_4656_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_4657_; lean_object* v_res_4658_; 
v_a_00___x40___internal___hyg_1__boxed_4657_ = lean_unbox(v_a_00___x40___internal___hyg_4655_);
v_res_4658_ = lean_io_exit(v_a_00___x40___internal___hyg_1__boxed_4657_);
return v_res_4658_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_forceExit___boxed(lean_object* v_00_u03b1_4662_, lean_object* v_a_00___x40___internal___hyg_4663_, lean_object* v_a_00___x40___internal___hyg_4664_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_4665_; lean_object* v_res_4666_; 
v_a_00___x40___internal___hyg_1__boxed_4665_ = lean_unbox(v_a_00___x40___internal___hyg_4663_);
v_res_4666_ = lean_io_force_exit(v_a_00___x40___internal___hyg_1__boxed_4665_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l_IO_getTID___boxed(lean_object* v_a_00___x40___internal___hyg_4668_){
_start:
{
uint64_t v_res_4669_; lean_object* v_r_4670_; 
v_res_4669_ = lean_io_get_tid();
v_r_4670_ = lean_box_uint64(v_res_4669_);
return v_r_4670_;
}
}
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object* v_acc_4671_){
_start:
{
uint32_t v___y_4673_; uint32_t v___y_4674_; uint32_t v___y_4675_; uint8_t v_read_4678_; uint8_t v_write_4679_; uint8_t v_execution_4680_; uint32_t v___y_4682_; uint32_t v___y_4683_; uint32_t v___y_4687_; 
v_read_4678_ = lean_ctor_get_uint8(v_acc_4671_, 0);
v_write_4679_ = lean_ctor_get_uint8(v_acc_4671_, 1);
v_execution_4680_ = lean_ctor_get_uint8(v_acc_4671_, 2);
if (v_read_4678_ == 0)
{
uint32_t v___x_4690_; 
v___x_4690_ = 0;
v___y_4687_ = v___x_4690_;
goto v___jp_4686_;
}
else
{
uint32_t v___x_4691_; 
v___x_4691_ = 4;
v___y_4687_ = v___x_4691_;
goto v___jp_4686_;
}
v___jp_4672_:
{
uint32_t v___x_4676_; uint32_t v___x_4677_; 
v___x_4676_ = lean_uint32_lor(v___y_4674_, v___y_4675_);
v___x_4677_ = lean_uint32_lor(v___y_4673_, v___x_4676_);
return v___x_4677_;
}
v___jp_4681_:
{
if (v_execution_4680_ == 0)
{
uint32_t v___x_4684_; 
v___x_4684_ = 0;
v___y_4673_ = v___y_4682_;
v___y_4674_ = v___y_4683_;
v___y_4675_ = v___x_4684_;
goto v___jp_4672_;
}
else
{
uint32_t v___x_4685_; 
v___x_4685_ = 1;
v___y_4673_ = v___y_4682_;
v___y_4674_ = v___y_4683_;
v___y_4675_ = v___x_4685_;
goto v___jp_4672_;
}
}
v___jp_4686_:
{
if (v_write_4679_ == 0)
{
uint32_t v___x_4688_; 
v___x_4688_ = 0;
v___y_4682_ = v___y_4687_;
v___y_4683_ = v___x_4688_;
goto v___jp_4681_;
}
else
{
uint32_t v___x_4689_; 
v___x_4689_ = 2;
v___y_4682_ = v___y_4687_;
v___y_4683_ = v___x_4689_;
goto v___jp_4681_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object* v_acc_4692_){
_start:
{
uint32_t v_res_4693_; lean_object* v_r_4694_; 
v_res_4693_ = l_IO_AccessRight_flags(v_acc_4692_);
lean_dec_ref(v_acc_4692_);
v_r_4694_ = lean_box_uint32(v_res_4693_);
return v_r_4694_;
}
}
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object* v_acc_4695_){
_start:
{
lean_object* v_user_4696_; lean_object* v_group_4697_; lean_object* v_other_4698_; uint32_t v___x_4699_; uint32_t v___x_4700_; uint32_t v_u_4701_; uint32_t v___x_4702_; uint32_t v___x_4703_; uint32_t v_g_4704_; uint32_t v_o_4705_; uint32_t v___x_4706_; uint32_t v___x_4707_; 
v_user_4696_ = lean_ctor_get(v_acc_4695_, 0);
v_group_4697_ = lean_ctor_get(v_acc_4695_, 1);
v_other_4698_ = lean_ctor_get(v_acc_4695_, 2);
v___x_4699_ = l_IO_AccessRight_flags(v_user_4696_);
v___x_4700_ = 6;
v_u_4701_ = lean_uint32_shift_left(v___x_4699_, v___x_4700_);
v___x_4702_ = l_IO_AccessRight_flags(v_group_4697_);
v___x_4703_ = 3;
v_g_4704_ = lean_uint32_shift_left(v___x_4702_, v___x_4703_);
v_o_4705_ = l_IO_AccessRight_flags(v_other_4698_);
v___x_4706_ = lean_uint32_lor(v_g_4704_, v_o_4705_);
v___x_4707_ = lean_uint32_lor(v_u_4701_, v___x_4706_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object* v_acc_4708_){
_start:
{
uint32_t v_res_4709_; lean_object* v_r_4710_; 
v_res_4709_ = l_IO_FileRight_flags(v_acc_4708_);
lean_dec_ref(v_acc_4708_);
v_r_4710_ = lean_box_uint32(v_res_4709_);
return v_r_4710_;
}
}
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object* v_filename_4714_, lean_object* v_mode_4715_, lean_object* v_a_00___x40___internal___hyg_4716_){
_start:
{
uint32_t v_mode_boxed_4717_; lean_object* v_res_4718_; 
v_mode_boxed_4717_ = lean_unbox_uint32(v_mode_4715_);
lean_dec(v_mode_4715_);
v_res_4718_ = lean_chmod(v_filename_4714_, v_mode_boxed_4717_);
lean_dec_ref(v_filename_4714_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object* v_filename_4719_, lean_object* v_mode_4720_){
_start:
{
uint32_t v___x_4722_; lean_object* v___x_4723_; 
v___x_4722_ = l_IO_FileRight_flags(v_mode_4720_);
v___x_4723_ = lean_chmod(v_filename_4719_, v___x_4722_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object* v_filename_4724_, lean_object* v_mode_4725_, lean_object* v_a_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l_IO_setAccessRights(v_filename_4724_, v_mode_4725_);
lean_dec_ref(v_mode_4725_);
lean_dec_ref(v_filename_4724_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object* v_00_u03b1_4728_, lean_object* v_mx_4729_){
_start:
{
lean_object* v___x_4731_; 
v___x_4731_ = lean_apply_1(v_mx_4729_, lean_box(0));
return v___x_4731_;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object* v_00_u03b1_4732_, lean_object* v_mx_4733_, lean_object* v_s_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(v_00_u03b1_4732_, v_mx_4733_);
return v_res_4735_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg(lean_object* v_a_4738_){
_start:
{
lean_object* v___x_4740_; 
v___x_4740_ = lean_st_mk_ref(v_a_4738_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg___boxed(lean_object* v_a_4741_, lean_object* v_a_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l_IO_mkRef___redArg(v_a_4741_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object* v_00_u03b1_4744_, lean_object* v_a_4745_){
_start:
{
lean_object* v___x_4747_; 
v___x_4747_ = lean_st_mk_ref(v_a_4745_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___boxed(lean_object* v_00_u03b1_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_){
_start:
{
lean_object* v_res_4751_; 
v_res_4751_ = l_IO_mkRef(v_00_u03b1_4748_, v_a_4749_);
return v_res_4751_;
}
}
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object* v_h_4752_){
_start:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
lean_inc_n(v_h_4752_, 5);
v___x_4753_ = lean_alloc_closure((void*)(l_IO_FS_Handle_flush___boxed), 2, 1);
lean_closure_set(v___x_4753_, 0, v_h_4752_);
v___x_4754_ = lean_alloc_closure((void*)(l_IO_FS_Handle_read___boxed), 3, 1);
lean_closure_set(v___x_4754_, 0, v_h_4752_);
v___x_4755_ = lean_alloc_closure((void*)(l_IO_FS_Handle_write___boxed), 3, 1);
lean_closure_set(v___x_4755_, 0, v_h_4752_);
v___x_4756_ = lean_alloc_closure((void*)(l_IO_FS_Handle_getLine___boxed), 2, 1);
lean_closure_set(v___x_4756_, 0, v_h_4752_);
v___x_4757_ = lean_alloc_closure((void*)(l_IO_FS_Handle_putStr___boxed), 3, 1);
lean_closure_set(v___x_4757_, 0, v_h_4752_);
v___x_4758_ = lean_alloc_closure((void*)(l_IO_FS_Handle_isTty___boxed), 2, 1);
lean_closure_set(v___x_4758_, 0, v_h_4752_);
v___x_4759_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4759_, 0, v___x_4753_);
lean_ctor_set(v___x_4759_, 1, v___x_4754_);
lean_ctor_set(v___x_4759_, 2, v___x_4755_);
lean_ctor_set(v___x_4759_, 3, v___x_4756_);
lean_ctor_set(v___x_4759_, 4, v___x_4757_);
lean_ctor_set(v___x_4759_, 5, v___x_4758_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0(lean_object* v_r_4760_, size_t v_n_4761_){
_start:
{
lean_object* v___x_4763_; lean_object* v_data_4764_; lean_object* v_pos_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4779_; 
v___x_4763_ = lean_st_ref_take(v_r_4760_);
v_data_4764_ = lean_ctor_get(v___x_4763_, 0);
v_pos_4765_ = lean_ctor_get(v___x_4763_, 1);
v_isSharedCheck_4779_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4767_ = v___x_4763_;
v_isShared_4768_ = v_isSharedCheck_4779_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_pos_4765_);
lean_inc(v_data_4764_);
lean_dec(v___x_4763_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4779_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v_data_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4775_; 
v___x_4769_ = lean_usize_to_nat(v_n_4761_);
v___x_4770_ = lean_nat_add(v_pos_4765_, v___x_4769_);
lean_dec(v___x_4769_);
lean_inc(v_pos_4765_);
v_data_4771_ = l_ByteArray_extract(v_data_4764_, v_pos_4765_, v___x_4770_);
lean_dec(v___x_4770_);
v___x_4772_ = lean_byte_array_size(v_data_4771_);
v___x_4773_ = lean_nat_add(v_pos_4765_, v___x_4772_);
lean_dec(v_pos_4765_);
if (v_isShared_4768_ == 0)
{
lean_ctor_set(v___x_4767_, 1, v___x_4773_);
v___x_4775_ = v___x_4767_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_data_4764_);
lean_ctor_set(v_reuseFailAlloc_4778_, 1, v___x_4773_);
v___x_4775_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = lean_st_ref_set(v_r_4760_, v___x_4775_);
v___x_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4777_, 0, v_data_4771_);
return v___x_4777_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0___boxed(lean_object* v_r_4780_, lean_object* v_n_4781_, lean_object* v___y_4782_){
_start:
{
size_t v_n_boxed_4783_; lean_object* v_res_4784_; 
v_n_boxed_4783_ = lean_unbox_usize(v_n_4781_);
lean_dec(v_n_4781_);
v_res_4784_ = l_IO_FS_Stream_ofBuffer___lam__0(v_r_4780_, v_n_boxed_4783_);
lean_dec(v_r_4780_);
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1(lean_object* v_r_4785_, lean_object* v_data_4786_){
_start:
{
lean_object* v___x_4788_; lean_object* v_data_4789_; lean_object* v_pos_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4804_; 
v___x_4788_ = lean_st_ref_take(v_r_4785_);
v_data_4789_ = lean_ctor_get(v___x_4788_, 0);
v_pos_4790_ = lean_ctor_get(v___x_4788_, 1);
v_isSharedCheck_4804_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4804_ == 0)
{
v___x_4792_ = v___x_4788_;
v_isShared_4793_ = v_isSharedCheck_4804_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_pos_4790_);
lean_inc(v_data_4789_);
lean_dec(v___x_4788_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4804_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; uint8_t v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4800_; 
v___x_4794_ = lean_unsigned_to_nat(0u);
v___x_4795_ = lean_byte_array_size(v_data_4786_);
v___x_4796_ = 0;
lean_inc(v_pos_4790_);
v___x_4797_ = lean_byte_array_copy_slice(v_data_4786_, v___x_4794_, v_data_4789_, v_pos_4790_, v___x_4795_, v___x_4796_);
v___x_4798_ = lean_nat_add(v_pos_4790_, v___x_4795_);
lean_dec(v_pos_4790_);
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 1, v___x_4798_);
lean_ctor_set(v___x_4792_, 0, v___x_4797_);
v___x_4800_ = v___x_4792_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___x_4797_);
lean_ctor_set(v_reuseFailAlloc_4803_, 1, v___x_4798_);
v___x_4800_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = lean_st_ref_set(v_r_4785_, v___x_4800_);
v___x_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
return v___x_4802_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1___boxed(lean_object* v_r_4805_, lean_object* v_data_4806_, lean_object* v___y_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l_IO_FS_Stream_ofBuffer___lam__1(v_r_4805_, v_data_4806_);
lean_dec_ref(v_data_4806_);
lean_dec(v_r_4805_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2(lean_object* v_r_4809_, lean_object* v_s_4810_){
_start:
{
lean_object* v___x_4812_; lean_object* v_data_4813_; lean_object* v_pos_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4829_; 
v___x_4812_ = lean_st_ref_take(v_r_4809_);
v_data_4813_ = lean_ctor_get(v___x_4812_, 0);
v_pos_4814_ = lean_ctor_get(v___x_4812_, 1);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4816_ = v___x_4812_;
v_isShared_4817_ = v_isSharedCheck_4829_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_pos_4814_);
lean_inc(v_data_4813_);
lean_dec(v___x_4812_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4829_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v_data_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; uint8_t v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4825_; 
v_data_4818_ = lean_string_to_utf8(v_s_4810_);
v___x_4819_ = lean_unsigned_to_nat(0u);
v___x_4820_ = lean_byte_array_size(v_data_4818_);
v___x_4821_ = 0;
lean_inc(v_pos_4814_);
v___x_4822_ = lean_byte_array_copy_slice(v_data_4818_, v___x_4819_, v_data_4813_, v_pos_4814_, v___x_4820_, v___x_4821_);
lean_dec_ref(v_data_4818_);
v___x_4823_ = lean_nat_add(v_pos_4814_, v___x_4820_);
lean_dec(v_pos_4814_);
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 1, v___x_4823_);
lean_ctor_set(v___x_4816_, 0, v___x_4822_);
v___x_4825_ = v___x_4816_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___x_4822_);
lean_ctor_set(v_reuseFailAlloc_4828_, 1, v___x_4823_);
v___x_4825_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4826_ = lean_st_ref_set(v_r_4809_, v___x_4825_);
v___x_4827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4827_, 0, v___x_4826_);
return v___x_4827_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2___boxed(lean_object* v_r_4830_, lean_object* v_s_4831_, lean_object* v___y_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_IO_FS_Stream_ofBuffer___lam__2(v_r_4830_, v_s_4831_);
lean_dec_ref(v_s_4831_);
lean_dec(v_r_4830_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(lean_object* v_a_4834_, lean_object* v_i_4835_){
_start:
{
uint8_t v___y_4837_; lean_object* v___x_4842_; uint8_t v___x_4843_; 
v___x_4842_ = lean_byte_array_size(v_a_4834_);
v___x_4843_ = lean_nat_dec_lt(v_i_4835_, v___x_4842_);
if (v___x_4843_ == 0)
{
lean_object* v___x_4844_; 
lean_dec(v_i_4835_);
v___x_4844_ = lean_box(0);
return v___x_4844_;
}
else
{
uint8_t v___x_4845_; uint8_t v___x_4846_; uint8_t v___x_4847_; 
v___x_4845_ = lean_byte_array_fget(v_a_4834_, v_i_4835_);
v___x_4846_ = 0;
v___x_4847_ = lean_uint8_dec_eq(v___x_4845_, v___x_4846_);
if (v___x_4847_ == 0)
{
uint8_t v___x_4848_; uint8_t v___x_4849_; 
v___x_4848_ = 10;
v___x_4849_ = lean_uint8_dec_eq(v___x_4845_, v___x_4848_);
v___y_4837_ = v___x_4849_;
goto v___jp_4836_;
}
else
{
v___y_4837_ = v___x_4847_;
goto v___jp_4836_;
}
}
v___jp_4836_:
{
if (v___y_4837_ == 0)
{
lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4838_ = lean_unsigned_to_nat(1u);
v___x_4839_ = lean_nat_add(v_i_4835_, v___x_4838_);
lean_dec(v_i_4835_);
v_i_4835_ = v___x_4839_;
goto _start;
}
else
{
lean_object* v___x_4841_; 
v___x_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4841_, 0, v_i_4835_);
return v___x_4841_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0___boxed(lean_object* v_a_4850_, lean_object* v_i_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(v_a_4850_, v_i_4851_);
lean_dec_ref(v_a_4850_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3(lean_object* v_r_4856_){
_start:
{
lean_object* v___x_4858_; lean_object* v_data_4859_; lean_object* v_pos_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4884_; 
v___x_4858_ = lean_st_ref_take(v_r_4856_);
v_data_4859_ = lean_ctor_get(v___x_4858_, 0);
v_pos_4860_ = lean_ctor_get(v___x_4858_, 1);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4862_ = v___x_4858_;
v_isShared_4863_ = v_isSharedCheck_4884_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_pos_4860_);
lean_inc(v_data_4859_);
lean_dec(v___x_4858_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4884_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___y_4865_; lean_object* v___x_4876_; 
lean_inc(v_pos_4860_);
v___x_4876_ = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(v_data_4859_, v_pos_4860_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v___x_4877_; 
v___x_4877_ = lean_byte_array_size(v_data_4859_);
v___y_4865_ = v___x_4877_;
goto v___jp_4864_;
}
else
{
lean_object* v_val_4878_; uint8_t v___x_4879_; uint8_t v___x_4880_; uint8_t v___x_4881_; 
v_val_4878_ = lean_ctor_get(v___x_4876_, 0);
lean_inc(v_val_4878_);
lean_dec_ref_known(v___x_4876_, 1);
v___x_4879_ = lean_byte_array_get(v_data_4859_, v_val_4878_);
v___x_4880_ = 0;
v___x_4881_ = lean_uint8_dec_eq(v___x_4879_, v___x_4880_);
if (v___x_4881_ == 0)
{
lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4882_ = lean_unsigned_to_nat(1u);
v___x_4883_ = lean_nat_add(v_val_4878_, v___x_4882_);
lean_dec(v_val_4878_);
v___y_4865_ = v___x_4883_;
goto v___jp_4864_;
}
else
{
v___y_4865_ = v_val_4878_;
goto v___jp_4864_;
}
}
v___jp_4864_:
{
lean_object* v___x_4866_; lean_object* v___x_4868_; 
v___x_4866_ = l_ByteArray_extract(v_data_4859_, v_pos_4860_, v___y_4865_);
if (v_isShared_4863_ == 0)
{
lean_ctor_set(v___x_4862_, 1, v___y_4865_);
v___x_4868_ = v___x_4862_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_data_4859_);
lean_ctor_set(v_reuseFailAlloc_4875_, 1, v___y_4865_);
v___x_4868_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
lean_object* v___x_4869_; uint8_t v___x_4870_; 
v___x_4869_ = lean_st_ref_set(v_r_4856_, v___x_4868_);
v___x_4870_ = lean_string_validate_utf8(v___x_4866_);
if (v___x_4870_ == 0)
{
lean_object* v___x_4871_; lean_object* v___x_4872_; 
lean_dec_ref(v___x_4866_);
v___x_4871_ = ((lean_object*)(l_IO_FS_Stream_ofBuffer___lam__3___closed__1));
v___x_4872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4872_, 0, v___x_4871_);
return v___x_4872_;
}
else
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = lean_string_from_utf8_unchecked(v___x_4866_);
v___x_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4873_);
return v___x_4874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3___boxed(lean_object* v_r_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v_res_4887_; 
v_res_4887_ = l_IO_FS_Stream_ofBuffer___lam__3(v_r_4885_);
lean_dec(v_r_4885_);
return v_res_4887_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4(lean_object* v___x_4888_){
_start:
{
lean_object* v___x_4890_; 
v___x_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4888_);
return v___x_4890_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4___boxed(lean_object* v___x_4891_, lean_object* v___y_4892_){
_start:
{
lean_object* v_res_4893_; 
v_res_4893_ = l_IO_FS_Stream_ofBuffer___lam__4(v___x_4891_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object* v_r_4896_){
_start:
{
lean_object* v___f_4897_; lean_object* v___f_4898_; lean_object* v___f_4899_; lean_object* v___f_4900_; lean_object* v___f_4901_; lean_object* v___f_4902_; lean_object* v___x_4903_; 
lean_inc_n(v_r_4896_, 3);
v___f_4897_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4897_, 0, v_r_4896_);
v___f_4898_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4898_, 0, v_r_4896_);
v___f_4899_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4899_, 0, v_r_4896_);
v___f_4900_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__3___boxed), 2, 1);
lean_closure_set(v___f_4900_, 0, v_r_4896_);
v___f_4901_ = ((lean_object*)(l_IO_FS_Stream_ofBuffer___closed__0));
v___f_4902_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___closed__5));
v___x_4903_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4903_, 0, v___f_4901_);
lean_ctor_set(v___x_4903_, 1, v___f_4897_);
lean_ctor_set(v___x_4903_, 2, v___f_4898_);
lean_ctor_set(v___x_4903_, 3, v___f_4900_);
lean_ctor_set(v___x_4903_, 4, v___f_4899_);
lean_ctor_set(v___x_4903_, 5, v___f_4902_);
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(lean_object* v_s_4906_, lean_object* v_acc_4907_){
_start:
{
lean_object* v_read_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; 
v_read_4909_ = lean_ctor_get(v_s_4906_, 1);
v___x_4910_ = ((lean_object*)(l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1));
lean_inc_ref(v_read_4909_);
v___x_4911_ = lean_apply_2(v_read_4909_, v___x_4910_, lean_box(0));
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4925_; 
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4914_ = v___x_4911_;
v_isShared_4915_ = v_isSharedCheck_4925_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4911_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4925_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
uint8_t v___x_4916_; 
v___x_4916_ = l_ByteArray_isEmpty(v_a_4912_);
if (v___x_4916_ == 0)
{
lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
lean_del_object(v___x_4914_);
v___x_4917_ = lean_unsigned_to_nat(0u);
v___x_4918_ = lean_byte_array_size(v_acc_4907_);
v___x_4919_ = lean_byte_array_size(v_a_4912_);
v___x_4920_ = lean_byte_array_copy_slice(v_a_4912_, v___x_4917_, v_acc_4907_, v___x_4918_, v___x_4919_, v___x_4916_);
lean_dec(v_a_4912_);
v_acc_4907_ = v___x_4920_;
goto _start;
}
else
{
lean_object* v___x_4923_; 
lean_dec(v_a_4912_);
lean_dec_ref(v_s_4906_);
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 0, v_acc_4907_);
v___x_4923_ = v___x_4914_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_acc_4907_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
}
else
{
lean_dec_ref(v_acc_4907_);
lean_dec_ref(v_s_4906_);
return v___x_4911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed(lean_object* v_s_4926_, lean_object* v_acc_4927_, lean_object* v_a_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4926_, v_acc_4927_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto(lean_object* v_s_4930_, lean_object* v_buf_4931_){
_start:
{
lean_object* v___x_4933_; 
v___x_4933_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4930_, v_buf_4931_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto___boxed(lean_object* v_s_4934_, lean_object* v_buf_4935_, lean_object* v_a_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l_IO_FS_Stream_readBinToEndInto(v_s_4934_, v_buf_4935_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd(lean_object* v_s_4938_){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___x_4940_ = l_ByteArray_empty;
v___x_4941_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4938_, v___x_4940_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd___boxed(lean_object* v_s_4942_, lean_object* v_a_4943_){
_start:
{
lean_object* v_res_4944_; 
v_res_4944_ = l_IO_FS_Stream_readBinToEnd(v_s_4942_);
return v_res_4944_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd(lean_object* v_s_4948_){
_start:
{
lean_object* v___x_4950_; 
v___x_4950_ = l_IO_FS_Stream_readBinToEnd(v_s_4948_);
if (lean_obj_tag(v___x_4950_) == 0)
{
lean_object* v_a_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4964_; 
v_a_4951_ = lean_ctor_get(v___x_4950_, 0);
v_isSharedCheck_4964_ = !lean_is_exclusive(v___x_4950_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4953_ = v___x_4950_;
v_isShared_4954_ = v_isSharedCheck_4964_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_a_4951_);
lean_dec(v___x_4950_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4964_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
uint8_t v___x_4955_; 
v___x_4955_ = lean_string_validate_utf8(v_a_4951_);
if (v___x_4955_ == 0)
{
lean_object* v___x_4956_; lean_object* v___x_4958_; 
lean_dec(v_a_4951_);
v___x_4956_ = ((lean_object*)(l_IO_FS_Stream_readToEnd___closed__1));
if (v_isShared_4954_ == 0)
{
lean_ctor_set_tag(v___x_4953_, 1);
lean_ctor_set(v___x_4953_, 0, v___x_4956_);
v___x_4958_ = v___x_4953_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v___x_4956_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
else
{
lean_object* v___x_4960_; lean_object* v___x_4962_; 
v___x_4960_ = lean_string_from_utf8_unchecked(v_a_4951_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 0, v___x_4960_);
v___x_4962_ = v___x_4953_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v___x_4960_);
v___x_4962_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
return v___x_4962_;
}
}
}
}
else
{
lean_object* v_a_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4972_; 
v_a_4965_ = lean_ctor_get(v___x_4950_, 0);
v_isSharedCheck_4972_ = !lean_is_exclusive(v___x_4950_);
if (v_isSharedCheck_4972_ == 0)
{
v___x_4967_ = v___x_4950_;
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_a_4965_);
lean_dec(v___x_4950_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___x_4970_; 
if (v_isShared_4968_ == 0)
{
v___x_4970_ = v___x_4967_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_a_4965_);
v___x_4970_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
return v___x_4970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd___boxed(lean_object* v_s_4973_, lean_object* v_a_4974_){
_start:
{
lean_object* v_res_4975_; 
v_res_4975_ = l_IO_FS_Stream_readToEnd(v_s_4973_);
return v_res_4975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read(lean_object* v_s_4976_, lean_object* v_lines_4977_){
_start:
{
lean_object* v_getLine_4979_; lean_object* v___x_4980_; 
v_getLine_4979_ = lean_ctor_get(v_s_4976_, 3);
lean_inc_ref(v_getLine_4979_);
v___x_4980_ = lean_apply_1(v_getLine_4979_, lean_box(0));
if (lean_obj_tag(v___x_4980_) == 0)
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_5035_; 
v_a_4981_ = lean_ctor_get(v___x_4980_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_4983_ = v___x_4980_;
v_isShared_4984_ = v_isSharedCheck_5035_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4980_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_5035_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___y_4986_; lean_object* v___y_4990_; lean_object* v___y_4991_; lean_object* v___y_4992_; uint32_t v___y_4993_; uint32_t v___y_5001_; lean_object* v___x_5023_; lean_object* v___x_5024_; uint8_t v___x_5025_; 
v___x_5023_ = lean_string_utf8_byte_size(v_a_4981_);
v___x_5024_ = lean_unsigned_to_nat(0u);
v___x_5025_ = lean_nat_dec_eq(v___x_5023_, v___x_5024_);
if (v___x_5025_ == 0)
{
lean_object* v___x_5026_; lean_object* v___x_5027_; 
lean_inc(v_a_4981_);
v___x_5026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5026_, 0, v_a_4981_);
lean_ctor_set(v___x_5026_, 1, v___x_5024_);
lean_ctor_set(v___x_5026_, 2, v___x_5023_);
v___x_5027_ = l_String_Slice_Pos_prev_x3f(v___x_5026_, v___x_5023_);
if (lean_obj_tag(v___x_5027_) == 0)
{
uint32_t v___x_5028_; 
lean_dec_ref_known(v___x_5026_, 3);
v___x_5028_ = 65;
v___y_5001_ = v___x_5028_;
goto v___jp_5000_;
}
else
{
lean_object* v_val_5029_; lean_object* v___x_5030_; 
v_val_5029_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_val_5029_);
lean_dec_ref_known(v___x_5027_, 1);
v___x_5030_ = l_String_Slice_Pos_get_x3f(v___x_5026_, v_val_5029_);
lean_dec(v_val_5029_);
lean_dec_ref_known(v___x_5026_, 3);
if (lean_obj_tag(v___x_5030_) == 0)
{
uint32_t v___x_5031_; 
v___x_5031_ = 65;
v___y_5001_ = v___x_5031_;
goto v___jp_5000_;
}
else
{
lean_object* v_val_5032_; uint32_t v___x_5033_; 
v_val_5032_ = lean_ctor_get(v___x_5030_, 0);
lean_inc(v_val_5032_);
lean_dec_ref_known(v___x_5030_, 1);
v___x_5033_ = lean_unbox_uint32(v_val_5032_);
lean_dec(v_val_5032_);
v___y_5001_ = v___x_5033_;
goto v___jp_5000_;
}
}
}
else
{
lean_object* v___x_5034_; 
lean_del_object(v___x_4983_);
lean_dec(v_a_4981_);
lean_dec_ref(v_s_4976_);
v___x_5034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5034_, 0, v_lines_4977_);
return v___x_5034_;
}
v___jp_4985_:
{
lean_object* v___x_4987_; 
v___x_4987_ = lean_array_push(v_lines_4977_, v___y_4986_);
v_lines_4977_ = v___x_4987_;
goto _start;
}
v___jp_4989_:
{
uint32_t v___x_4994_; uint8_t v___x_4995_; 
v___x_4994_ = 13;
v___x_4995_ = lean_uint32_dec_eq(v___y_4993_, v___x_4994_);
if (v___x_4995_ == 0)
{
lean_dec(v___y_4991_);
lean_dec(v___y_4990_);
v___y_4986_ = v___y_4992_;
goto v___jp_4985_;
}
else
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___x_4996_ = lean_string_utf8_byte_size(v___y_4992_);
lean_inc(v___y_4990_);
lean_inc_ref(v___y_4992_);
v___x_4997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4997_, 0, v___y_4992_);
lean_ctor_set(v___x_4997_, 1, v___y_4990_);
lean_ctor_set(v___x_4997_, 2, v___x_4996_);
v___x_4998_ = l_String_Slice_Pos_prevn(v___x_4997_, v___x_4996_, v___y_4991_);
lean_dec_ref_known(v___x_4997_, 3);
v___x_4999_ = lean_string_utf8_extract_fast(v___y_4992_, v___y_4990_, v___x_4998_);
lean_dec(v___x_4998_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4992_);
v___y_4986_ = v___x_4999_;
goto v___jp_4985_;
}
}
v___jp_5000_:
{
uint32_t v___x_5002_; uint8_t v___x_5003_; 
v___x_5002_ = 10;
v___x_5003_ = lean_uint32_dec_eq(v___y_5001_, v___x_5002_);
if (v___x_5003_ == 0)
{
lean_object* v___x_5004_; lean_object* v___x_5006_; 
lean_dec_ref(v_s_4976_);
v___x_5004_ = lean_array_push(v_lines_4977_, v_a_4981_);
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 0, v___x_5004_);
v___x_5006_ = v___x_4983_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v___x_5004_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
else
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
lean_del_object(v___x_4983_);
v___x_5008_ = lean_unsigned_to_nat(1u);
v___x_5009_ = lean_unsigned_to_nat(0u);
v___x_5010_ = lean_string_utf8_byte_size(v_a_4981_);
lean_inc(v_a_4981_);
v___x_5011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5011_, 0, v_a_4981_);
lean_ctor_set(v___x_5011_, 1, v___x_5009_);
lean_ctor_set(v___x_5011_, 2, v___x_5010_);
v___x_5012_ = l_String_Slice_Pos_prevn(v___x_5011_, v___x_5010_, v___x_5008_);
lean_dec_ref_known(v___x_5011_, 3);
v___x_5013_ = lean_string_utf8_extract_fast(v_a_4981_, v___x_5009_, v___x_5012_);
lean_dec(v___x_5012_);
lean_dec(v_a_4981_);
v___x_5014_ = lean_string_utf8_byte_size(v___x_5013_);
lean_inc_ref(v___x_5013_);
v___x_5015_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5015_, 0, v___x_5013_);
lean_ctor_set(v___x_5015_, 1, v___x_5009_);
lean_ctor_set(v___x_5015_, 2, v___x_5014_);
v___x_5016_ = l_String_Slice_Pos_prev_x3f(v___x_5015_, v___x_5014_);
if (lean_obj_tag(v___x_5016_) == 0)
{
uint32_t v___x_5017_; 
lean_dec_ref_known(v___x_5015_, 3);
v___x_5017_ = 65;
v___y_4990_ = v___x_5009_;
v___y_4991_ = v___x_5008_;
v___y_4992_ = v___x_5013_;
v___y_4993_ = v___x_5017_;
goto v___jp_4989_;
}
else
{
lean_object* v_val_5018_; lean_object* v___x_5019_; 
v_val_5018_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_val_5018_);
lean_dec_ref_known(v___x_5016_, 1);
v___x_5019_ = l_String_Slice_Pos_get_x3f(v___x_5015_, v_val_5018_);
lean_dec(v_val_5018_);
lean_dec_ref_known(v___x_5015_, 3);
if (lean_obj_tag(v___x_5019_) == 0)
{
uint32_t v___x_5020_; 
v___x_5020_ = 65;
v___y_4990_ = v___x_5009_;
v___y_4991_ = v___x_5008_;
v___y_4992_ = v___x_5013_;
v___y_4993_ = v___x_5020_;
goto v___jp_4989_;
}
else
{
lean_object* v_val_5021_; uint32_t v___x_5022_; 
v_val_5021_ = lean_ctor_get(v___x_5019_, 0);
lean_inc(v_val_5021_);
lean_dec_ref_known(v___x_5019_, 1);
v___x_5022_ = lean_unbox_uint32(v_val_5021_);
lean_dec(v_val_5021_);
v___y_4990_ = v___x_5009_;
v___y_4991_ = v___x_5008_;
v___y_4992_ = v___x_5013_;
v___y_4993_ = v___x_5022_;
goto v___jp_4989_;
}
}
}
}
}
}
else
{
lean_object* v_a_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5043_; 
lean_dec_ref(v_lines_4977_);
lean_dec_ref(v_s_4976_);
v_a_5036_ = lean_ctor_get(v___x_4980_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_5038_ = v___x_4980_;
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_a_5036_);
lean_dec(v___x_4980_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v___x_5041_; 
if (v_isShared_5039_ == 0)
{
v___x_5041_ = v___x_5038_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_a_5036_);
v___x_5041_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
return v___x_5041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read___boxed(lean_object* v_s_5044_, lean_object* v_lines_5045_, lean_object* v_a_5046_){
_start:
{
lean_object* v_res_5047_; 
v_res_5047_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_5044_, v_lines_5045_);
return v_res_5047_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines(lean_object* v_s_5048_){
_start:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5050_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_5051_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_5048_, v___x_5050_);
return v___x_5051_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines___boxed(lean_object* v_s_5052_, lean_object* v_a_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l_IO_FS_Stream_lines(v_s_5052_);
return v_res_5054_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0(lean_object* v_bOut_5055_){
_start:
{
lean_object* v___x_5057_; 
v___x_5057_ = lean_st_ref_get(v_bOut_5055_);
return v___x_5057_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed(lean_object* v_bOut_5058_, lean_object* v___y_5059_){
_start:
{
lean_object* v_res_5060_; 
v_res_5060_ = l_IO_FS_withIsolatedStreams___redArg___lam__0(v_bOut_5058_);
lean_dec(v_bOut_5058_);
return v_res_5060_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5065_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3));
v___x_5066_ = lean_unsigned_to_nat(46u);
v___x_5067_ = lean_unsigned_to_nat(193u);
v___x_5068_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2));
v___x_5069_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1));
v___x_5070_ = l_mkPanicMessageWithDecl(v___x_5069_, v___x_5068_, v___x_5067_, v___x_5066_, v___x_5065_);
return v___x_5070_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1(lean_object* v_r_5071_, lean_object* v_toPure_5072_, lean_object* v_bOut_5073_){
_start:
{
lean_object* v___y_5075_; lean_object* v_data_5078_; uint8_t v___x_5079_; 
v_data_5078_ = lean_ctor_get(v_bOut_5073_, 0);
lean_inc_ref(v_data_5078_);
lean_dec_ref(v_bOut_5073_);
v___x_5079_ = lean_string_validate_utf8(v_data_5078_);
if (v___x_5079_ == 0)
{
lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
lean_dec_ref(v_data_5078_);
v___x_5080_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0));
v___x_5081_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4, &l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4_once, _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4);
v___x_5082_ = l_panic___redArg(v___x_5080_, v___x_5081_);
v___y_5075_ = v___x_5082_;
goto v___jp_5074_;
}
else
{
lean_object* v___x_5083_; 
v___x_5083_ = lean_string_from_utf8_unchecked(v_data_5078_);
v___y_5075_ = v___x_5083_;
goto v___jp_5074_;
}
v___jp_5074_:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5076_, 0, v___y_5075_);
lean_ctor_set(v___x_5076_, 1, v_r_5071_);
v___x_5077_ = lean_apply_2(v_toPure_5072_, lean_box(0), v___x_5076_);
return v___x_5077_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__2(lean_object* v_toPure_5084_, lean_object* v_inst_5085_, lean_object* v___f_5086_, lean_object* v_toBind_5087_, lean_object* v_r_5088_){
_start:
{
lean_object* v___f_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; 
v___f_5089_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5089_, 0, v_r_5088_);
lean_closure_set(v___f_5089_, 1, v_toPure_5084_);
v___x_5090_ = lean_apply_2(v_inst_5085_, lean_box(0), v___f_5086_);
v___x_5091_ = lean_apply_4(v_toBind_5087_, lean_box(0), lean_box(0), v___x_5090_, v___f_5089_);
return v___x_5091_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3(lean_object* v_toPure_5092_, lean_object* v_inst_5093_, lean_object* v_toBind_5094_, lean_object* v_bIn_5095_, lean_object* v_inst_5096_, lean_object* v_inst_5097_, uint8_t v_isolateStderr_5098_, lean_object* v_x_5099_, lean_object* v_bOut_5100_){
_start:
{
lean_object* v___f_5101_; lean_object* v___f_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___y_5106_; 
lean_inc(v_bOut_5100_);
v___f_5101_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5101_, 0, v_bOut_5100_);
lean_inc(v_toBind_5094_);
lean_inc(v_inst_5093_);
v___f_5102_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__2), 5, 4);
lean_closure_set(v___f_5102_, 0, v_toPure_5092_);
lean_closure_set(v___f_5102_, 1, v_inst_5093_);
lean_closure_set(v___f_5102_, 2, v___f_5101_);
lean_closure_set(v___f_5102_, 3, v_toBind_5094_);
v___x_5103_ = l_IO_FS_Stream_ofBuffer(v_bIn_5095_);
v___x_5104_ = l_IO_FS_Stream_ofBuffer(v_bOut_5100_);
if (v_isolateStderr_5098_ == 0)
{
v___y_5106_ = v_x_5099_;
goto v___jp_5105_;
}
else
{
lean_object* v___x_5110_; 
lean_inc_ref(v___x_5104_);
lean_inc(v_inst_5093_);
lean_inc(v_inst_5097_);
lean_inc_ref(v_inst_5096_);
v___x_5110_ = l_IO_withStderr___redArg(v_inst_5096_, v_inst_5097_, v_inst_5093_, v___x_5104_, v_x_5099_);
v___y_5106_ = v___x_5110_;
goto v___jp_5105_;
}
v___jp_5105_:
{
lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; 
lean_inc(v_inst_5093_);
lean_inc(v_inst_5097_);
lean_inc_ref(v_inst_5096_);
v___x_5107_ = l_IO_withStdout___redArg(v_inst_5096_, v_inst_5097_, v_inst_5093_, v___x_5104_, v___y_5106_);
v___x_5108_ = l_IO_withStdin___redArg(v_inst_5096_, v_inst_5097_, v_inst_5093_, v___x_5103_, v___x_5107_);
v___x_5109_ = lean_apply_4(v_toBind_5094_, lean_box(0), lean_box(0), v___x_5108_, v___f_5102_);
return v___x_5109_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed(lean_object* v_toPure_5111_, lean_object* v_inst_5112_, lean_object* v_toBind_5113_, lean_object* v_bIn_5114_, lean_object* v_inst_5115_, lean_object* v_inst_5116_, lean_object* v_isolateStderr_5117_, lean_object* v_x_5118_, lean_object* v_bOut_5119_){
_start:
{
uint8_t v_isolateStderr_boxed_5120_; lean_object* v_res_5121_; 
v_isolateStderr_boxed_5120_ = lean_unbox(v_isolateStderr_5117_);
v_res_5121_ = l_IO_FS_withIsolatedStreams___redArg___lam__3(v_toPure_5111_, v_inst_5112_, v_toBind_5113_, v_bIn_5114_, v_inst_5115_, v_inst_5116_, v_isolateStderr_boxed_5120_, v_x_5118_, v_bOut_5119_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4(lean_object* v_toPure_5122_, lean_object* v_inst_5123_, lean_object* v_toBind_5124_, lean_object* v_inst_5125_, lean_object* v_inst_5126_, uint8_t v_isolateStderr_5127_, lean_object* v_x_5128_, lean_object* v___x_5129_, lean_object* v_bIn_5130_){
_start:
{
lean_object* v___x_5131_; lean_object* v___f_5132_; lean_object* v___x_5133_; 
v___x_5131_ = lean_box(v_isolateStderr_5127_);
lean_inc(v_toBind_5124_);
v___f_5132_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_5132_, 0, v_toPure_5122_);
lean_closure_set(v___f_5132_, 1, v_inst_5123_);
lean_closure_set(v___f_5132_, 2, v_toBind_5124_);
lean_closure_set(v___f_5132_, 3, v_bIn_5130_);
lean_closure_set(v___f_5132_, 4, v_inst_5125_);
lean_closure_set(v___f_5132_, 5, v_inst_5126_);
lean_closure_set(v___f_5132_, 6, v___x_5131_);
lean_closure_set(v___f_5132_, 7, v_x_5128_);
v___x_5133_ = lean_apply_4(v_toBind_5124_, lean_box(0), lean_box(0), v___x_5129_, v___f_5132_);
return v___x_5133_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed(lean_object* v_toPure_5134_, lean_object* v_inst_5135_, lean_object* v_toBind_5136_, lean_object* v_inst_5137_, lean_object* v_inst_5138_, lean_object* v_isolateStderr_5139_, lean_object* v_x_5140_, lean_object* v___x_5141_, lean_object* v_bIn_5142_){
_start:
{
uint8_t v_isolateStderr_boxed_5143_; lean_object* v_res_5144_; 
v_isolateStderr_boxed_5143_ = lean_unbox(v_isolateStderr_5139_);
v_res_5144_ = l_IO_FS_withIsolatedStreams___redArg___lam__4(v_toPure_5134_, v_inst_5135_, v_toBind_5136_, v_inst_5137_, v_inst_5138_, v_isolateStderr_boxed_5143_, v_x_5140_, v___x_5141_, v_bIn_5142_);
return v_res_5144_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__0(void){
_start:
{
lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; 
v___x_5145_ = lean_unsigned_to_nat(0u);
v___x_5146_ = l_ByteArray_empty;
v___x_5147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5147_, 0, v___x_5146_);
lean_ctor_set(v___x_5147_, 1, v___x_5145_);
return v___x_5147_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__1(void){
_start:
{
lean_object* v___x_5148_; lean_object* v___x_5149_; 
v___x_5148_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___closed__0, &l_IO_FS_withIsolatedStreams___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___redArg___closed__0);
v___x_5149_ = lean_alloc_closure((void*)(l_IO_mkRef___boxed), 3, 2);
lean_closure_set(v___x_5149_, 0, lean_box(0));
lean_closure_set(v___x_5149_, 1, v___x_5148_);
return v___x_5149_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object* v_inst_5150_, lean_object* v_inst_5151_, lean_object* v_inst_5152_, lean_object* v_x_5153_, uint8_t v_isolateStderr_5154_){
_start:
{
lean_object* v_toApplicative_5155_; lean_object* v_toBind_5156_; lean_object* v_toPure_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___f_5161_; lean_object* v___x_5162_; 
v_toApplicative_5155_ = lean_ctor_get(v_inst_5150_, 0);
v_toBind_5156_ = lean_ctor_get(v_inst_5150_, 1);
lean_inc_n(v_toBind_5156_, 2);
v_toPure_5157_ = lean_ctor_get(v_toApplicative_5155_, 1);
lean_inc(v_toPure_5157_);
v___x_5158_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___closed__1, &l_IO_FS_withIsolatedStreams___redArg___closed__1_once, _init_l_IO_FS_withIsolatedStreams___redArg___closed__1);
lean_inc(v_inst_5152_);
v___x_5159_ = lean_apply_2(v_inst_5152_, lean_box(0), v___x_5158_);
v___x_5160_ = lean_box(v_isolateStderr_5154_);
lean_inc(v___x_5159_);
v___f_5161_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_5161_, 0, v_toPure_5157_);
lean_closure_set(v___f_5161_, 1, v_inst_5152_);
lean_closure_set(v___f_5161_, 2, v_toBind_5156_);
lean_closure_set(v___f_5161_, 3, v_inst_5150_);
lean_closure_set(v___f_5161_, 4, v_inst_5151_);
lean_closure_set(v___f_5161_, 5, v___x_5160_);
lean_closure_set(v___f_5161_, 6, v_x_5153_);
lean_closure_set(v___f_5161_, 7, v___x_5159_);
v___x_5162_ = lean_apply_4(v_toBind_5156_, lean_box(0), lean_box(0), v___x_5159_, v___f_5161_);
return v___x_5162_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___boxed(lean_object* v_inst_5163_, lean_object* v_inst_5164_, lean_object* v_inst_5165_, lean_object* v_x_5166_, lean_object* v_isolateStderr_5167_){
_start:
{
uint8_t v_isolateStderr_boxed_5168_; lean_object* v_res_5169_; 
v_isolateStderr_boxed_5168_ = lean_unbox(v_isolateStderr_5167_);
v_res_5169_ = l_IO_FS_withIsolatedStreams___redArg(v_inst_5163_, v_inst_5164_, v_inst_5165_, v_x_5166_, v_isolateStderr_boxed_5168_);
return v_res_5169_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object* v_m_5170_, lean_object* v_00_u03b1_5171_, lean_object* v_inst_5172_, lean_object* v_inst_5173_, lean_object* v_inst_5174_, lean_object* v_x_5175_, uint8_t v_isolateStderr_5176_){
_start:
{
lean_object* v___x_5177_; 
v___x_5177_ = l_IO_FS_withIsolatedStreams___redArg(v_inst_5172_, v_inst_5173_, v_inst_5174_, v_x_5175_, v_isolateStderr_5176_);
return v___x_5177_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___boxed(lean_object* v_m_5178_, lean_object* v_00_u03b1_5179_, lean_object* v_inst_5180_, lean_object* v_inst_5181_, lean_object* v_inst_5182_, lean_object* v_x_5183_, lean_object* v_isolateStderr_5184_){
_start:
{
uint8_t v_isolateStderr_boxed_5185_; lean_object* v_res_5186_; 
v_isolateStderr_boxed_5185_ = lean_unbox(v_isolateStderr_5184_);
v_res_5186_ = l_IO_FS_withIsolatedStreams(v_m_5178_, v_00_u03b1_5179_, v_inst_5180_, v_inst_5181_, v_inst_5182_, v_x_5183_, v_isolateStderr_boxed_5185_);
return v_res_5186_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9(void){
_start:
{
lean_object* v___x_5243_; lean_object* v___x_5244_; 
v___x_5243_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0));
v___x_5244_ = l_String_toRawSubstring_x27(v___x_5243_);
return v___x_5244_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17(void){
_start:
{
lean_object* v___x_5259_; lean_object* v___x_5260_; 
v___x_5259_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16));
v___x_5260_ = l_String_toRawSubstring_x27(v___x_5259_);
return v___x_5260_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24(void){
_start:
{
lean_object* v___x_5273_; lean_object* v___x_5274_; 
v___x_5273_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18));
v___x_5274_ = l_String_toRawSubstring_x27(v___x_5273_);
return v___x_5274_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31(void){
_start:
{
lean_object* v___x_5289_; lean_object* v___x_5290_; 
v___x_5289_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30));
v___x_5290_ = l_String_toRawSubstring_x27(v___x_5289_);
return v___x_5290_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object* v_x_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_){
_start:
{
lean_object* v___x_5318_; uint8_t v___x_5319_; 
v___x_5318_ = ((lean_object*)(l_termPrintln_x21_____00__closed__1));
lean_inc(v_x_5315_);
v___x_5319_ = l_Lean_Syntax_isOfKind(v_x_5315_, v___x_5318_);
if (v___x_5319_ == 0)
{
lean_object* v___x_5320_; lean_object* v___x_5321_; 
lean_dec(v_x_5315_);
v___x_5320_ = lean_box(1);
v___x_5321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5321_, 0, v___x_5320_);
lean_ctor_set(v___x_5321_, 1, v_a_5317_);
return v___x_5321_;
}
else
{
lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; uint8_t v___x_5325_; 
v___x_5322_ = lean_unsigned_to_nat(1u);
v___x_5323_ = l_Lean_Syntax_getArg(v_x_5315_, v___x_5322_);
lean_dec(v_x_5315_);
v___x_5324_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1));
lean_inc(v___x_5323_);
v___x_5325_ = l_Lean_Syntax_isOfKind(v___x_5323_, v___x_5324_);
if (v___x_5325_ == 0)
{
lean_object* v_quotContext_5326_; lean_object* v_currMacroScope_5327_; lean_object* v_ref_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; 
v_quotContext_5326_ = lean_ctor_get(v_a_5316_, 1);
v_currMacroScope_5327_ = lean_ctor_get(v_a_5316_, 2);
v_ref_5328_ = lean_ctor_get(v_a_5316_, 5);
v___x_5329_ = l_Lean_SourceInfo_fromRef(v_ref_5328_, v___x_5325_);
v___x_5330_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3));
v___x_5331_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5));
v___x_5332_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6));
lean_inc_n(v___x_5329_, 14);
v___x_5333_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5333_, 0, v___x_5329_);
lean_ctor_set(v___x_5333_, 1, v___x_5332_);
v___x_5334_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8));
v___x_5335_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
v___x_5336_ = lean_box(0);
lean_inc_n(v_currMacroScope_5327_, 4);
lean_inc_n(v_quotContext_5326_, 4);
v___x_5337_ = l_Lean_addMacroScope(v_quotContext_5326_, v___x_5336_, v_currMacroScope_5327_);
v___x_5338_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15));
v___x_5339_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5339_, 0, v___x_5329_);
lean_ctor_set(v___x_5339_, 1, v___x_5335_);
lean_ctor_set(v___x_5339_, 2, v___x_5337_);
lean_ctor_set(v___x_5339_, 3, v___x_5338_);
v___x_5340_ = l_Lean_Syntax_node1(v___x_5329_, v___x_5334_, v___x_5339_);
v___x_5341_ = l_Lean_Syntax_node2(v___x_5329_, v___x_5331_, v___x_5333_, v___x_5340_);
v___x_5342_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_5343_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
v___x_5344_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20));
v___x_5345_ = l_Lean_addMacroScope(v_quotContext_5326_, v___x_5344_, v_currMacroScope_5327_);
v___x_5346_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22));
v___x_5347_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5347_, 0, v___x_5329_);
lean_ctor_set(v___x_5347_, 1, v___x_5343_);
lean_ctor_set(v___x_5347_, 2, v___x_5345_);
lean_ctor_set(v___x_5347_, 3, v___x_5346_);
v___x_5348_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_5349_ = l_Lean_Syntax_node1(v___x_5329_, v___x_5348_, v___x_5323_);
v___x_5350_ = l_Lean_Syntax_node2(v___x_5329_, v___x_5342_, v___x_5347_, v___x_5349_);
v___x_5351_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23));
v___x_5352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5352_, 0, v___x_5329_);
lean_ctor_set(v___x_5352_, 1, v___x_5351_);
v___x_5353_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
v___x_5354_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25));
v___x_5355_ = l_Lean_addMacroScope(v_quotContext_5326_, v___x_5354_, v_currMacroScope_5327_);
v___x_5356_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29));
v___x_5357_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5357_, 0, v___x_5329_);
lean_ctor_set(v___x_5357_, 1, v___x_5353_);
lean_ctor_set(v___x_5357_, 2, v___x_5355_);
lean_ctor_set(v___x_5357_, 3, v___x_5356_);
v___x_5358_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
v___x_5359_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32));
v___x_5360_ = l_Lean_addMacroScope(v_quotContext_5326_, v___x_5359_, v_currMacroScope_5327_);
v___x_5361_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36));
v___x_5362_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5362_, 0, v___x_5329_);
lean_ctor_set(v___x_5362_, 1, v___x_5358_);
lean_ctor_set(v___x_5362_, 2, v___x_5360_);
lean_ctor_set(v___x_5362_, 3, v___x_5361_);
v___x_5363_ = l_Lean_Syntax_node1(v___x_5329_, v___x_5348_, v___x_5362_);
v___x_5364_ = l_Lean_Syntax_node2(v___x_5329_, v___x_5342_, v___x_5357_, v___x_5363_);
v___x_5365_ = l_Lean_Syntax_node1(v___x_5329_, v___x_5348_, v___x_5364_);
v___x_5366_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37));
v___x_5367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5367_, 0, v___x_5329_);
lean_ctor_set(v___x_5367_, 1, v___x_5366_);
v___x_5368_ = l_Lean_Syntax_node5(v___x_5329_, v___x_5330_, v___x_5341_, v___x_5350_, v___x_5352_, v___x_5365_, v___x_5367_);
v___x_5369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5369_, 0, v___x_5368_);
lean_ctor_set(v___x_5369_, 1, v_a_5317_);
return v___x_5369_;
}
else
{
lean_object* v_quotContext_5370_; lean_object* v_currMacroScope_5371_; lean_object* v_ref_5372_; uint8_t v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; 
v_quotContext_5370_ = lean_ctor_get(v_a_5316_, 1);
v_currMacroScope_5371_ = lean_ctor_get(v_a_5316_, 2);
v_ref_5372_ = lean_ctor_get(v_a_5316_, 5);
v___x_5373_ = 0;
v___x_5374_ = l_Lean_SourceInfo_fromRef(v_ref_5372_, v___x_5373_);
v___x_5375_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3));
v___x_5376_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5));
v___x_5377_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6));
lean_inc_n(v___x_5374_, 17);
v___x_5378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5378_, 0, v___x_5374_);
lean_ctor_set(v___x_5378_, 1, v___x_5377_);
v___x_5379_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8));
v___x_5380_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
v___x_5381_ = lean_box(0);
lean_inc_n(v_currMacroScope_5371_, 4);
lean_inc_n(v_quotContext_5370_, 4);
v___x_5382_ = l_Lean_addMacroScope(v_quotContext_5370_, v___x_5381_, v_currMacroScope_5371_);
v___x_5383_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15));
v___x_5384_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5384_, 0, v___x_5374_);
lean_ctor_set(v___x_5384_, 1, v___x_5380_);
lean_ctor_set(v___x_5384_, 2, v___x_5382_);
lean_ctor_set(v___x_5384_, 3, v___x_5383_);
v___x_5385_ = l_Lean_Syntax_node1(v___x_5374_, v___x_5379_, v___x_5384_);
v___x_5386_ = l_Lean_Syntax_node2(v___x_5374_, v___x_5376_, v___x_5378_, v___x_5385_);
v___x_5387_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_5388_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
v___x_5389_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20));
v___x_5390_ = l_Lean_addMacroScope(v_quotContext_5370_, v___x_5389_, v_currMacroScope_5371_);
v___x_5391_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22));
v___x_5392_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5392_, 0, v___x_5374_);
lean_ctor_set(v___x_5392_, 1, v___x_5388_);
lean_ctor_set(v___x_5392_, 2, v___x_5390_);
lean_ctor_set(v___x_5392_, 3, v___x_5391_);
v___x_5393_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_5394_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39));
v___x_5395_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41));
v___x_5396_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42));
v___x_5397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5397_, 0, v___x_5374_);
lean_ctor_set(v___x_5397_, 1, v___x_5396_);
v___x_5398_ = l_Lean_Syntax_node2(v___x_5374_, v___x_5395_, v___x_5397_, v___x_5323_);
v___x_5399_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37));
v___x_5400_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5400_, 0, v___x_5374_);
lean_ctor_set(v___x_5400_, 1, v___x_5399_);
lean_inc_ref(v___x_5400_);
lean_inc(v___x_5386_);
v___x_5401_ = l_Lean_Syntax_node3(v___x_5374_, v___x_5394_, v___x_5386_, v___x_5398_, v___x_5400_);
v___x_5402_ = l_Lean_Syntax_node1(v___x_5374_, v___x_5393_, v___x_5401_);
v___x_5403_ = l_Lean_Syntax_node2(v___x_5374_, v___x_5387_, v___x_5392_, v___x_5402_);
v___x_5404_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23));
v___x_5405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5405_, 0, v___x_5374_);
lean_ctor_set(v___x_5405_, 1, v___x_5404_);
v___x_5406_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
v___x_5407_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25));
v___x_5408_ = l_Lean_addMacroScope(v_quotContext_5370_, v___x_5407_, v_currMacroScope_5371_);
v___x_5409_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29));
v___x_5410_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5410_, 0, v___x_5374_);
lean_ctor_set(v___x_5410_, 1, v___x_5406_);
lean_ctor_set(v___x_5410_, 2, v___x_5408_);
lean_ctor_set(v___x_5410_, 3, v___x_5409_);
v___x_5411_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
v___x_5412_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32));
v___x_5413_ = l_Lean_addMacroScope(v_quotContext_5370_, v___x_5412_, v_currMacroScope_5371_);
v___x_5414_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36));
v___x_5415_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5415_, 0, v___x_5374_);
lean_ctor_set(v___x_5415_, 1, v___x_5411_);
lean_ctor_set(v___x_5415_, 2, v___x_5413_);
lean_ctor_set(v___x_5415_, 3, v___x_5414_);
v___x_5416_ = l_Lean_Syntax_node1(v___x_5374_, v___x_5393_, v___x_5415_);
v___x_5417_ = l_Lean_Syntax_node2(v___x_5374_, v___x_5387_, v___x_5410_, v___x_5416_);
v___x_5418_ = l_Lean_Syntax_node1(v___x_5374_, v___x_5393_, v___x_5417_);
v___x_5419_ = l_Lean_Syntax_node5(v___x_5374_, v___x_5375_, v___x_5386_, v___x_5403_, v___x_5405_, v___x_5418_, v___x_5400_);
v___x_5420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5420_, 0, v___x_5419_);
lean_ctor_set(v___x_5420_, 1, v_a_5317_);
return v___x_5420_;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___boxed(lean_object* v_x_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_){
_start:
{
lean_object* v_res_5424_; 
v_res_5424_ = l___aux__Init__System__IO______macroRules__termPrintln_x21______1(v_x_5421_, v_a_5422_, v_a_5423_);
lean_dec_ref(v_a_5422_);
return v_res_5424_;
}
}
LEAN_EXPORT lean_object* l_Runtime_markMultiThreaded___boxed(lean_object* v_00_u03b1_5428_, lean_object* v_a_5429_, lean_object* v_a_00___x40___internal___hyg_5430_){
_start:
{
lean_object* v_res_5431_; 
v_res_5431_ = lean_runtime_mark_multi_threaded(v_a_5429_);
return v_res_5431_;
}
}
LEAN_EXPORT lean_object* l_Runtime_markPersistent___boxed(lean_object* v_00_u03b1_5435_, lean_object* v_a_5436_, lean_object* v_a_00___x40___internal___hyg_5437_){
_start:
{
lean_object* v_res_5438_; 
v_res_5438_ = lean_runtime_mark_persistent(v_a_5436_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l_Runtime_forget___boxed(lean_object* v_00_u03b1_5442_, lean_object* v_a_5443_, lean_object* v_a_00___x40___internal___hyg_5444_){
_start:
{
lean_object* v_res_5445_; 
v_res_5445_ = lean_runtime_forget(v_a_5443_);
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l_Runtime_hold___boxed(lean_object* v_00_u03b1_5449_, lean_object* v_a_5450_, lean_object* v_a_00___x40___internal___hyg_5451_){
_start:
{
lean_object* v_res_5452_; 
v_res_5452_ = lean_runtime_hold(v_a_5450_);
lean_dec(v_a_5450_);
return v_res_5452_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_IO(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
