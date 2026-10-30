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
lean_object* lean_obj_tag_nat(lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_dbg_sleep(uint32_t, lean_object*);
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
lean_object* l_MonadExcept_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadLiftBaseIOEIO___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadLiftBaseIOEIO___redArg___closed__0 = (const lean_object*)&l_instMonadLiftBaseIOEIO___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___redArg();
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___redArg___boxed(lean_object*);
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
static const lean_closure_object l_instMonadEIO___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___redArg___closed__0 = (const lean_object*)&l_instMonadEIO___redArg___closed__0_value;
static const lean_closure_object l_instMonadEIO___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__3___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___redArg___closed__1 = (const lean_object*)&l_instMonadEIO___redArg___closed__1_value;
static const lean_ctor_object l_instMonadEIO___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadEIO___redArg___closed__0_value),((lean_object*)&l_instMonadEIO___redArg___closed__1_value)}};
static const lean_object* l_instMonadEIO___redArg___closed__2 = (const lean_object*)&l_instMonadEIO___redArg___closed__2_value;
static const lean_closure_object l_instMonadEIO___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__5___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___redArg___closed__3 = (const lean_object*)&l_instMonadEIO___redArg___closed__3_value;
static const lean_closure_object l_instMonadEIO___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__7___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___redArg___closed__4 = (const lean_object*)&l_instMonadEIO___redArg___closed__4_value;
static const lean_closure_object l_instMonadEIO___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__9___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___redArg___closed__5 = (const lean_object*)&l_instMonadEIO___redArg___closed__5_value;
static const lean_closure_object l_instMonadEIO___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__11___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___redArg___closed__6 = (const lean_object*)&l_instMonadEIO___redArg___closed__6_value;
static const lean_ctor_object l_instMonadEIO___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadEIO___redArg___closed__2_value),((lean_object*)&l_instMonadEIO___redArg___closed__3_value),((lean_object*)&l_instMonadEIO___redArg___closed__4_value),((lean_object*)&l_instMonadEIO___redArg___closed__5_value),((lean_object*)&l_instMonadEIO___redArg___closed__6_value)}};
static const lean_object* l_instMonadEIO___redArg___closed__7 = (const lean_object*)&l_instMonadEIO___redArg___closed__7_value;
static const lean_closure_object l_instMonadEIO___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadEIO___aux__13___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadEIO___redArg___closed__8 = (const lean_object*)&l_instMonadEIO___redArg___closed__8_value;
static const lean_ctor_object l_instMonadEIO___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadEIO___redArg___closed__7_value),((lean_object*)&l_instMonadEIO___redArg___closed__8_value)}};
static const lean_object* l_instMonadEIO___redArg___closed__9 = (const lean_object*)&l_instMonadEIO___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_instMonadEIO___redArg();
LEAN_EXPORT lean_object* l_instMonadEIO___redArg___boxed(lean_object*);
static lean_once_cell_t l_instMonadEIO___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instMonadEIO___closed__0;
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadFinallyEIO___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyEIO___aux__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadFinallyEIO___redArg___closed__0 = (const lean_object*)&l_instMonadFinallyEIO___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___redArg();
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadAttachEIO___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadAttachEIO___aux__3___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadAttachEIO___redArg___closed__0 = (const lean_object*)&l_instMonadAttachEIO___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadAttachEIO___redArg();
LEAN_EXPORT lean_object* l_instMonadAttachEIO___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instMonadAttachEIO(lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadExceptOfEIO___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadExceptOfEIO___aux__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadExceptOfEIO___redArg___closed__0 = (const lean_object*)&l_instMonadExceptOfEIO___redArg___closed__0_value;
static const lean_closure_object l_instMonadExceptOfEIO___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadExceptOfEIO___aux__3___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadExceptOfEIO___redArg___closed__1 = (const lean_object*)&l_instMonadExceptOfEIO___redArg___closed__1_value;
static const lean_ctor_object l_instMonadExceptOfEIO___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instMonadExceptOfEIO___redArg___closed__0_value),((lean_object*)&l_instMonadExceptOfEIO___redArg___closed__1_value)}};
static const lean_object* l_instMonadExceptOfEIO___redArg___closed__2 = (const lean_object*)&l_instMonadExceptOfEIO___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___redArg();
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___redArg___boxed(lean_object*);
static lean_once_cell_t l_instMonadExceptOfEIO___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instMonadExceptOfEIO___closed__0;
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object*);
static lean_once_cell_t l_instOrElseEIO___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instOrElseEIO___redArg___closed__0;
static lean_once_cell_t l_instOrElseEIO___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instOrElseEIO___redArg___closed__1;
LEAN_EXPORT lean_object* l_instOrElseEIO___redArg();
LEAN_EXPORT lean_object* l_instOrElseEIO___redArg___boxed(lean_object*);
static lean_once_cell_t l_instOrElseEIO___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instOrElseEIO___closed__0;
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
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx___impl___boxed(lean_object*);
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
static const lean_ctor_object l_IO_waitAny___auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* l_IO_waitAny___auto__1___closed__18 = (const lean_object*)&l_IO_waitAny___auto__1___closed__18_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_IO_waitAny___auto__1___closed__19 = (const lean_object*)&l_IO_waitAny___auto__1___closed__19_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "zero_lt_succ"};
static const lean_object* l_IO_waitAny___auto__1___closed__20 = (const lean_object*)&l_IO_waitAny___auto__1___closed__20_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__21_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(139, 13, 209, 151, 253, 249, 15, 51)}};
static const lean_object* l_IO_waitAny___auto__1___closed__21 = (const lean_object*)&l_IO_waitAny___auto__1___closed__21_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__18_value),((lean_object*)&l_IO_waitAny___auto__1___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_IO_waitAny___auto__1___closed__22 = (const lean_object*)&l_IO_waitAny___auto__1___closed__22_value;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__23;
static const lean_string_object l_IO_waitAny___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_IO_waitAny___auto__1___closed__24 = (const lean_object*)&l_IO_waitAny___auto__1___closed__24_value;
static const lean_ctor_object l_IO_waitAny___auto__1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_IO_waitAny___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__25_value_aux_0),((lean_object*)&l_IO_waitAny___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__25_value_aux_1),((lean_object*)&l_IO_waitAny___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_IO_waitAny___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_IO_waitAny___auto__1___closed__25_value_aux_2),((lean_object*)&l_IO_waitAny___auto__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_IO_waitAny___auto__1___closed__25 = (const lean_object*)&l_IO_waitAny___auto__1___closed__25_value;
static const lean_string_object l_IO_waitAny___auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_IO_waitAny___auto__1___closed__26 = (const lean_object*)&l_IO_waitAny___auto__1___closed__26_value;
static lean_once_cell_t l_IO_waitAny___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_waitAny___auto__1___closed__27;
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
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx___impl___boxed(lean_object*);
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
lean_object* lean_io_rename_if_new(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_renameIfNew___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___redArg___lam__0(lean_object* v_00_u03b1_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_apply_1(v___y_257_, lean_box(0));
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___redArg___lam__0___boxed(lean_object* v_00_u03b1_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_instMonadLiftBaseIOEIO___redArg___lam__0(v_00_u03b1_261_, v___y_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___redArg(){
_start:
{
lean_object* v___f_267_; 
v___f_267_ = ((lean_object*)(l_instMonadLiftBaseIOEIO___redArg___closed__0));
return v___f_267_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___redArg___boxed(lean_object* v___dummy_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_instMonadLiftBaseIOEIO___redArg();
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object* v_00_u03b5_270_){
_start:
{
lean_object* v___f_271_; 
v___f_271_ = ((lean_object*)(l_instMonadLiftBaseIOEIO___redArg___closed__0));
return v___f_271_;
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg(lean_object* v_act_272_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_apply_1(v_act_272_, lean_box(0));
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set_tag(v___x_277_, 1);
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_a_283_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_274_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_274_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set_tag(v___x_285_, 0);
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg___boxed(lean_object* v_act_291_, lean_object* v_s_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_EIO_toBaseIO___redArg(v_act_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO(lean_object* v_00_u03b5_294_, lean_object* v_00_u03b1_295_, lean_object* v_act_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_apply_1(v_act_296_, lean_box(0));
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set_tag(v___x_301_, 1);
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
v_a_307_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_298_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_298_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set_tag(v___x_309_, 0);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___boxed(lean_object* v_00_u03b5_315_, lean_object* v_00_u03b1_316_, lean_object* v_act_317_, lean_object* v_s_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_EIO_toBaseIO(v_00_u03b5_315_, v_00_u03b1_316_, v_act_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg(lean_object* v_act_320_, lean_object* v_h_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_apply_1(v_act_320_, lean_box(0));
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; 
lean_dec_ref(v_h_321_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref_known(v___x_323_, 1);
return v_a_324_;
}
else
{
lean_object* v_a_325_; lean_object* v___x_326_; 
v_a_325_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_323_, 1);
v___x_326_ = lean_apply_2(v_h_321_, v_a_325_, lean_box(0));
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg___boxed(lean_object* v_act_327_, lean_object* v_h_328_, lean_object* v_s_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_EIO_catchExceptions___redArg(v_act_327_, v_h_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions(lean_object* v_00_u03b5_331_, lean_object* v_00_u03b1_332_, lean_object* v_act_333_, lean_object* v_h_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = lean_apply_1(v_act_333_, lean_box(0));
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; 
lean_dec_ref(v_h_334_);
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
return v_a_337_;
}
else
{
lean_object* v_a_338_; lean_object* v___x_339_; 
v_a_338_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_336_, 1);
v___x_339_ = lean_apply_2(v_h_334_, v_a_338_, lean_box(0));
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___boxed(lean_object* v_00_u03b5_340_, lean_object* v_00_u03b1_341_, lean_object* v_act_342_, lean_object* v_h_343_, lean_object* v_s_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_EIO_catchExceptions(v_00_u03b5_340_, v_00_u03b1_341_, v_act_342_, v_h_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1___redArg(lean_object* v_f_346_, lean_object* v_x_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_apply_1(v_x_347_, lean_box(0));
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_358_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = lean_apply_1(v_f_346_, v_a_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v_f_346_);
v_a_359_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_349_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_349_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1___redArg___boxed(lean_object* v_f_367_, lean_object* v_x_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_instMonadEIO___aux__1___redArg(v_f_367_, v_x_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1(lean_object* v_00_u03b5_371_, lean_object* v_00_u03b1_372_, lean_object* v_00_u03b2_373_, lean_object* v_f_374_, lean_object* v_x_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_apply_1(v_x_375_, lean_box(0));
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_386_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_386_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = lean_apply_1(v_f_374_, v_a_378_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_382_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec(v_f_374_);
v_a_387_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_377_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_377_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1___boxed(lean_object* v_00_u03b5_395_, lean_object* v_00_u03b1_396_, lean_object* v_00_u03b2_397_, lean_object* v_f_398_, lean_object* v_x_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_instMonadEIO___aux__1(v_00_u03b5_395_, v_00_u03b1_396_, v_00_u03b2_397_, v_f_398_, v_x_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3___redArg(lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = lean_apply_1(v_a_403_, lean_box(0));
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v___x_405_, 0);
lean_dec(v_unused_413_);
v___x_407_ = v___x_405_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_dec(v___x_405_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v_a_402_);
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_402_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_a_402_);
v_a_414_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_405_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_405_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3___redArg___boxed(lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_instMonadEIO___aux__3___redArg(v_a_422_, v_a_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3(lean_object* v_00_u03b5_426_, lean_object* v_00_u03b1_427_, lean_object* v_00_u03b2_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = lean_apply_1(v_a_430_, lean_box(0));
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v___x_432_, 0);
lean_dec(v_unused_440_);
v___x_434_ = v___x_432_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_dec(v___x_432_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v_a_429_);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_429_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec(v_a_429_);
v_a_441_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_432_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_432_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3___boxed(lean_object* v_00_u03b5_449_, lean_object* v_00_u03b1_450_, lean_object* v_00_u03b2_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_instMonadEIO___aux__3(v_00_u03b5_449_, v_00_u03b1_450_, v_00_u03b2_451_, v_a_452_, v_a_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5___redArg(lean_object* v_a_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v_a_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5___redArg___boxed(lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_instMonadEIO___aux__5___redArg(v_a_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5(lean_object* v_00_u03b5_462_, lean_object* v_00_u03b1_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v_a_464_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5___boxed(lean_object* v_00_u03b5_467_, lean_object* v_00_u03b1_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_instMonadEIO___aux__5(v_00_u03b5_467_, v_00_u03b1_468_, v_a_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7___redArg(lean_object* v_f_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_apply_1(v_f_472_, lean_box(0));
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v___x_477_ = lean_box(0);
v___x_478_ = lean_apply_2(v_x_473_, v___x_477_, lean_box(0));
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_487_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_487_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_487_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = lean_apply_1(v_a_476_, v_a_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v_a_476_);
v_a_488_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_478_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_478_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v_x_473_);
v_a_496_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_475_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_475_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7___redArg___boxed(lean_object* v_f_504_, lean_object* v_x_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_instMonadEIO___aux__7___redArg(v_f_504_, v_x_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7(lean_object* v_00_u03b5_508_, lean_object* v_00_u03b1_509_, lean_object* v_00_u03b2_510_, lean_object* v_f_511_, lean_object* v_x_512_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = lean_apply_1(v_f_511_, lean_box(0));
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v___x_514_, 1);
v___x_516_ = lean_box(0);
v___x_517_ = lean_apply_2(v_x_512_, v___x_516_, lean_box(0));
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_526_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_526_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_526_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_526_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = lean_apply_1(v_a_515_, v_a_518_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_522_);
v___x_524_ = v___x_520_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_a_515_);
v_a_527_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_517_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_517_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec_ref(v_x_512_);
v_a_535_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_514_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_514_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7___boxed(lean_object* v_00_u03b5_543_, lean_object* v_00_u03b1_544_, lean_object* v_00_u03b2_545_, lean_object* v_f_546_, lean_object* v_x_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_instMonadEIO___aux__7(v_00_u03b5_543_, v_00_u03b1_544_, v_00_u03b2_545_, v_f_546_, v_x_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9___redArg(lean_object* v_x_550_, lean_object* v_y_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = lean_apply_1(v_x_550_, lean_box(0));
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v___x_555_ = lean_box(0);
v___x_556_ = lean_apply_2(v_y_551_, v___x_555_, lean_box(0));
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v___x_556_, 0);
lean_dec(v_unused_564_);
v___x_558_ = v___x_556_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_dec(v___x_556_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_a_554_);
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_554_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec(v_a_554_);
v_a_565_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_556_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_556_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
else
{
lean_dec_ref(v_y_551_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9___redArg___boxed(lean_object* v_x_573_, lean_object* v_y_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_instMonadEIO___aux__9___redArg(v_x_573_, v_y_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9(lean_object* v_00_u03b5_577_, lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_x_580_, lean_object* v_y_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = lean_apply_1(v_x_580_, lean_box(0));
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v___x_585_ = lean_box(0);
v___x_586_ = lean_apply_2(v_y_581_, v___x_585_, lean_box(0));
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v___x_586_, 0);
lean_dec(v_unused_594_);
v___x_588_ = v___x_586_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_dec(v___x_586_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v_a_584_);
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_584_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec(v_a_584_);
v_a_595_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_586_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_586_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_dec_ref(v_y_581_);
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9___boxed(lean_object* v_00_u03b5_603_, lean_object* v_00_u03b1_604_, lean_object* v_00_u03b2_605_, lean_object* v_x_606_, lean_object* v_y_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_instMonadEIO___aux__9(v_00_u03b5_603_, v_00_u03b1_604_, v_00_u03b2_605_, v_x_606_, v_y_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11___redArg(lean_object* v_x_610_, lean_object* v_y_611_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_apply_1(v_x_610_, lean_box(0));
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec_ref_known(v___x_613_, 1);
v___x_614_ = lean_box(0);
v___x_615_ = lean_apply_2(v_y_611_, v___x_614_, lean_box(0));
return v___x_615_;
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v_y_611_);
v_a_616_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_613_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_613_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11___redArg___boxed(lean_object* v_x_624_, lean_object* v_y_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_instMonadEIO___aux__11___redArg(v_x_624_, v_y_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11(lean_object* v_00_u03b5_628_, lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v_x_631_, lean_object* v_y_632_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = lean_apply_1(v_x_631_, lean_box(0));
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec_ref_known(v___x_634_, 1);
v___x_635_ = lean_box(0);
v___x_636_ = lean_apply_2(v_y_632_, v___x_635_, lean_box(0));
return v___x_636_;
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec_ref(v_y_632_);
v_a_637_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_634_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_634_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11___boxed(lean_object* v_00_u03b5_645_, lean_object* v_00_u03b1_646_, lean_object* v_00_u03b2_647_, lean_object* v_x_648_, lean_object* v_y_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_instMonadEIO___aux__11(v_00_u03b5_645_, v_00_u03b1_646_, v_00_u03b2_647_, v_x_648_, v_y_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13___redArg(lean_object* v_x_652_, lean_object* v_f_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = lean_apply_1(v_x_652_, lean_box(0));
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = lean_apply_2(v_f_653_, v_a_656_, lean_box(0));
return v___x_657_;
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_f_653_);
v_a_658_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_655_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_655_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13___redArg___boxed(lean_object* v_x_666_, lean_object* v_f_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_instMonadEIO___aux__13___redArg(v_x_666_, v_f_667_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13(lean_object* v_00_u03b5_670_, lean_object* v_00_u03b1_671_, lean_object* v_00_u03b2_672_, lean_object* v_x_673_, lean_object* v_f_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = lean_apply_1(v_x_673_, lean_box(0));
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = lean_apply_2(v_f_674_, v_a_677_, lean_box(0));
return v___x_678_;
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_f_674_);
v_a_679_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_676_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_676_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13___boxed(lean_object* v_00_u03b5_687_, lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_x_690_, lean_object* v_f_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_instMonadEIO___aux__13(v_00_u03b5_687_, v_00_u03b1_688_, v_00_u03b2_689_, v_x_690_, v_f_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___redArg(){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = ((lean_object*)(l_instMonadEIO___redArg___closed__9));
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO___redArg___boxed(lean_object* v___dummy_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_instMonadEIO___redArg();
return v_res_716_;
}
}
static lean_object* _init_l_instMonadEIO___closed__0(void){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_instMonadEIO___redArg();
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object* v_00_u03b5_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_obj_once(&l_instMonadEIO___closed__0, &l_instMonadEIO___closed__0_once, _init_l_instMonadEIO___closed__0);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___redArg(lean_object* v_x_720_, lean_object* v_f_721_){
_start:
{
lean_object* v_r_723_; 
v_r_723_ = lean_apply_1(v_x_720_, lean_box(0));
if (lean_obj_tag(v_r_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_749_; 
v_a_724_ = lean_ctor_get(v_r_723_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v_r_723_);
if (v_isSharedCheck_749_ == 0)
{
v___x_726_ = v_r_723_;
v_isShared_727_ = v_isSharedCheck_749_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v_r_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_749_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
lean_inc(v_a_724_);
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 1);
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_748_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; 
v___x_730_ = lean_apply_2(v_f_721_, v___x_729_, lean_box(0));
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_739_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_739_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_739_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v_a_724_);
lean_ctor_set(v___x_735_, 1, v_a_731_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_a_724_);
v_a_740_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_730_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_730_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_a_750_ = lean_ctor_get(v_r_723_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v_r_723_, 1);
v___x_751_ = lean_box(0);
v___x_752_ = lean_apply_2(v_f_721_, v___x_751_, lean_box(0));
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v___x_752_, 0);
lean_dec(v_unused_760_);
v___x_754_ = v___x_752_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_dec(v___x_752_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set_tag(v___x_754_, 1);
lean_ctor_set(v___x_754_, 0, v_a_750_);
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_750_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_a_750_);
v_a_761_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_752_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_752_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___redArg___boxed(lean_object* v_x_769_, lean_object* v_f_770_, lean_object* v_s_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_instMonadFinallyEIO___aux__1___redArg(v_x_769_, v_f_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1(lean_object* v_00_u03b5_773_, lean_object* v_00_u03b1_774_, lean_object* v_00_u03b2_775_, lean_object* v_x_776_, lean_object* v_f_777_){
_start:
{
lean_object* v_r_779_; 
v_r_779_ = lean_apply_1(v_x_776_, lean_box(0));
if (lean_obj_tag(v_r_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_805_; 
v_a_780_ = lean_ctor_get(v_r_779_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_r_779_);
if (v_isSharedCheck_805_ == 0)
{
v___x_782_ = v_r_779_;
v_isShared_783_ = v_isSharedCheck_805_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v_r_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_805_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
lean_inc(v_a_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set_tag(v___x_782_, 1);
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_804_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; 
v___x_786_ = lean_apply_2(v_f_777_, v___x_785_, lean_box(0));
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_795_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_795_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_a_780_);
lean_ctor_set(v___x_791_, 1, v_a_787_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_791_);
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v_a_780_);
v_a_796_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_786_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_786_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_a_806_ = lean_ctor_get(v_r_779_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v_r_779_, 1);
v___x_807_ = lean_box(0);
v___x_808_ = lean_apply_2(v_f_777_, v___x_807_, lean_box(0));
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v___x_808_, 0);
lean_dec(v_unused_816_);
v___x_810_ = v___x_808_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_dec(v___x_808_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
lean_ctor_set_tag(v___x_810_, 1);
lean_ctor_set(v___x_810_, 0, v_a_806_);
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_806_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_a_806_);
v_a_817_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_808_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_808_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___boxed(lean_object* v_00_u03b5_825_, lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_x_828_, lean_object* v_f_829_, lean_object* v_s_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_instMonadFinallyEIO___aux__1(v_00_u03b5_825_, v_00_u03b1_826_, v_00_u03b2_827_, v_x_828_, v_f_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___redArg(){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = ((lean_object*)(l_instMonadFinallyEIO___redArg___closed__0));
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___redArg___boxed(lean_object* v___dummy_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_instMonadFinallyEIO___redArg();
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object* v_00_u03b5_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = ((lean_object*)(l_instMonadFinallyEIO___redArg___closed__0));
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___redArg(lean_object* v_x_839_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_apply_1(v_x_839_, lean_box(0));
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_a_850_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_841_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_841_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___redArg___boxed(lean_object* v_x_858_, lean_object* v_s_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_instMonadAttachEIO___aux__3___redArg(v_x_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3(lean_object* v_00_u03b5_861_, lean_object* v_00_u03b1_862_, lean_object* v_x_863_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = lean_apply_1(v_x_863_, lean_box(0));
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v_a_874_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_865_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_865_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___boxed(lean_object* v_00_u03b5_882_, lean_object* v_00_u03b1_883_, lean_object* v_x_884_, lean_object* v_s_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_instMonadAttachEIO___aux__3(v_00_u03b5_882_, v_00_u03b1_883_, v_x_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO___redArg(){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = ((lean_object*)(l_instMonadAttachEIO___redArg___closed__0));
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO___redArg___boxed(lean_object* v___dummy_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_instMonadAttachEIO___redArg();
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO(lean_object* v_00_u03b5_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = ((lean_object*)(l_instMonadAttachEIO___redArg___closed__0));
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___redArg(lean_object* v_e_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v_e_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___redArg___boxed(lean_object* v_e_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_instMonadExceptOfEIO___aux__1___redArg(v_e_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1(lean_object* v_00_u03b5_900_, lean_object* v_00_u03b1_901_, lean_object* v_e_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v_e_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___boxed(lean_object* v_00_u03b5_905_, lean_object* v_00_u03b1_906_, lean_object* v_e_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_instMonadExceptOfEIO___aux__1(v_00_u03b5_905_, v_00_u03b1_906_, v_e_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___redArg(lean_object* v_x_910_, lean_object* v_handle_911_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = lean_apply_1(v_x_910_, lean_box(0));
if (lean_obj_tag(v___x_913_) == 0)
{
lean_dec_ref(v_handle_911_);
return v___x_913_;
}
else
{
lean_object* v_a_914_; lean_object* v___x_915_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = lean_apply_2(v_handle_911_, v_a_914_, lean_box(0));
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___redArg___boxed(lean_object* v_x_916_, lean_object* v_handle_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_instMonadExceptOfEIO___aux__3___redArg(v_x_916_, v_handle_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3(lean_object* v_00_u03b5_920_, lean_object* v_00_u03b1_921_, lean_object* v_x_922_, lean_object* v_handle_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = lean_apply_1(v_x_922_, lean_box(0));
if (lean_obj_tag(v___x_925_) == 0)
{
lean_dec_ref(v_handle_923_);
return v___x_925_;
}
else
{
lean_object* v_a_926_; lean_object* v___x_927_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_925_, 1);
v___x_927_ = lean_apply_2(v_handle_923_, v_a_926_, lean_box(0));
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___boxed(lean_object* v_00_u03b5_928_, lean_object* v_00_u03b1_929_, lean_object* v_x_930_, lean_object* v_handle_931_, lean_object* v_a_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_instMonadExceptOfEIO___aux__3(v_00_u03b5_928_, v_00_u03b1_929_, v_x_930_, v_handle_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___redArg(){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = ((lean_object*)(l_instMonadExceptOfEIO___redArg___closed__2));
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___redArg___boxed(lean_object* v___dummy_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_instMonadExceptOfEIO___redArg();
return v_res_942_;
}
}
static lean_object* _init_l_instMonadExceptOfEIO___closed__0(void){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_instMonadExceptOfEIO___redArg();
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object* v_00_u03b5_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = lean_obj_once(&l_instMonadExceptOfEIO___closed__0, &l_instMonadExceptOfEIO___closed__0_once, _init_l_instMonadExceptOfEIO___closed__0);
return v___x_945_;
}
}
static lean_object* _init_l_instOrElseEIO___redArg___closed__0(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_obj_once(&l_instMonadExceptOfEIO___closed__0, &l_instMonadExceptOfEIO___closed__0_once, _init_l_instMonadExceptOfEIO___closed__0);
v___x_947_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l_instOrElseEIO___redArg___closed__1(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_obj_once(&l_instOrElseEIO___redArg___closed__0, &l_instOrElseEIO___redArg___closed__0_once, _init_l_instOrElseEIO___redArg___closed__0);
v___x_949_ = lean_alloc_closure((void*)(l_MonadExcept_orElse), 6, 4);
lean_closure_set(v___x_949_, 0, lean_box(0));
lean_closure_set(v___x_949_, 1, lean_box(0));
lean_closure_set(v___x_949_, 2, v___x_948_);
lean_closure_set(v___x_949_, 3, lean_box(0));
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_instOrElseEIO___redArg(){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = lean_obj_once(&l_instOrElseEIO___redArg___closed__1, &l_instOrElseEIO___redArg___closed__1_once, _init_l_instOrElseEIO___redArg___closed__1);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_instOrElseEIO___redArg___boxed(lean_object* v___dummy_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_instOrElseEIO___redArg();
return v_res_953_;
}
}
static lean_object* _init_l_instOrElseEIO___closed__0(void){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_instOrElseEIO___redArg();
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_instOrElseEIO(lean_object* v_00_u03b5_955_, lean_object* v_00_u03b1_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = lean_obj_once(&l_instOrElseEIO___closed__0, &l_instOrElseEIO___closed__0_once, _init_l_instOrElseEIO___closed__0);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1___redArg(lean_object* v_inst_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_960_, 0, v_inst_958_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1___redArg___boxed(lean_object* v_inst_961_, lean_object* v_s_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_instInhabitedEIO___aux__1___redArg(v_inst_961_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1(lean_object* v_00_u03b5_964_, lean_object* v_00_u03b1_965_, lean_object* v_inst_966_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v_inst_966_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object* v_00_u03b5_969_, lean_object* v_00_u03b1_970_, lean_object* v_inst_971_, lean_object* v_s_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_instInhabitedEIO___aux__1(v_00_u03b5_969_, v_00_u03b1_970_, v_inst_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___redArg(lean_object* v_inst_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_975_, 0, lean_box(0));
lean_closure_set(v___x_975_, 1, lean_box(0));
lean_closure_set(v___x_975_, 2, v_inst_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object* v_00_u03b5_976_, lean_object* v_00_u03b1_977_, lean_object* v_inst_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_979_, 0, lean_box(0));
lean_closure_set(v___x_979_, 1, lean_box(0));
lean_closure_set(v___x_979_, 2, v_inst_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_EIO_map___redArg(lean_object* v_f_980_, lean_object* v_x_981_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = lean_apply_1(v_x_981_, lean_box(0));
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_992_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_992_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_992_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_992_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_988_ = lean_apply_1(v_f_980_, v_a_984_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_988_);
v___x_990_ = v___x_986_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_f_980_);
v_a_993_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_983_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_983_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_map___redArg___boxed(lean_object* v_f_1001_, lean_object* v_x_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_EIO_map___redArg(v_f_1001_, v_x_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_EIO_map(lean_object* v_00_u03b1_1005_, lean_object* v_00_u03b2_1006_, lean_object* v_00_u03b5_1007_, lean_object* v_f_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_apply_1(v_x_1009_, lean_box(0));
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = lean_apply_1(v_f_1008_, v_a_1012_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1016_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v_f_1008_);
v_a_1021_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1011_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1011_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_map___boxed(lean_object* v_00_u03b1_1029_, lean_object* v_00_u03b2_1030_, lean_object* v_00_u03b5_1031_, lean_object* v_f_1032_, lean_object* v_x_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_EIO_map(v_00_u03b1_1029_, v_00_u03b2_1030_, v_00_u03b5_1031_, v_f_1032_, v_x_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_EIO_throw___redArg(lean_object* v_e_1036_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_e_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_EIO_throw___redArg___boxed(lean_object* v_e_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_EIO_throw___redArg(v_e_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_EIO_throw(lean_object* v_00_u03b5_1042_, lean_object* v_00_u03b1_1043_, lean_object* v_e_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1046_, 0, v_e_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_EIO_throw___boxed(lean_object* v_00_u03b5_1047_, lean_object* v_00_u03b1_1048_, lean_object* v_e_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_EIO_throw(v_00_u03b5_1047_, v_00_u03b1_1048_, v_e_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg(lean_object* v_x_1052_, lean_object* v_handle_1053_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_apply_1(v_x_1052_, lean_box(0));
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_dec_ref(v_handle_1053_);
return v___x_1055_;
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1057_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref_known(v___x_1055_, 1);
v___x_1057_ = lean_apply_2(v_handle_1053_, v_a_1056_, lean_box(0));
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg___boxed(lean_object* v_x_1058_, lean_object* v_handle_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_EIO_tryCatch___redArg(v_x_1058_, v_handle_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch(lean_object* v_00_u03b5_1062_, lean_object* v_00_u03b1_1063_, lean_object* v_x_1064_, lean_object* v_handle_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_apply_1(v_x_1064_, lean_box(0));
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_dec_ref(v_handle_1065_);
return v___x_1067_;
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1069_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1069_ = lean_apply_2(v_handle_1065_, v_a_1068_, lean_box(0));
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___boxed(lean_object* v_00_u03b5_1070_, lean_object* v_00_u03b1_1071_, lean_object* v_x_1072_, lean_object* v_handle_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_EIO_tryCatch(v_00_u03b5_1070_, v_00_u03b1_1071_, v_x_1072_, v_handle_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg(lean_object* v_e_1076_){
_start:
{
if (lean_obj_tag(v_e_1076_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_a_1078_ = lean_ctor_get(v_e_1076_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_e_1076_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v_e_1076_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v_e_1076_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set_tag(v___x_1080_, 1);
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_a_1086_ = lean_ctor_get(v_e_1076_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_e_1076_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v_e_1076_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v_e_1076_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 0);
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg___boxed(lean_object* v_e_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_EIO_ofExcept___redArg(v_e_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_EIO_ofExcept(lean_object* v_00_u03b5_1097_, lean_object* v_00_u03b1_1098_, lean_object* v_e_1099_){
_start:
{
if (lean_obj_tag(v_e_1099_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_a_1101_ = lean_ctor_get(v_e_1099_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_e_1099_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v_e_1099_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v_e_1099_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 1);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v_a_1109_ = lean_ctor_get(v_e_1099_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_e_1099_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v_e_1099_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v_e_1099_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set_tag(v___x_1111_, 0);
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
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
LEAN_EXPORT lean_object* l_EIO_ofExcept___boxed(lean_object* v_00_u03b5_1117_, lean_object* v_00_u03b1_1118_, lean_object* v_e_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_EIO_ofExcept(v_00_u03b5_1117_, v_00_u03b1_1118_, v_e_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_EIO_adapt___redArg(lean_object* v_f_1122_, lean_object* v_m_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_apply_1(v_m_1123_, lean_box(0));
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_f_1122_);
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1142_; 
v_a_1134_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1136_ = v___x_1125_;
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1125_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_apply_1(v_f_1122_, v_a_1134_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adapt___redArg___boxed(lean_object* v_f_1143_, lean_object* v_m_1144_, lean_object* v_s_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_EIO_adapt___redArg(v_f_1143_, v_m_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_EIO_adapt(lean_object* v_00_u03b5_1147_, lean_object* v_00_u03b5_x27_1148_, lean_object* v_00_u03b1_1149_, lean_object* v_f_1150_, lean_object* v_m_1151_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_apply_1(v_m_1151_, lean_box(0));
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_f_1150_);
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1170_; 
v_a_1162_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1164_ = v___x_1153_;
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1153_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = lean_apply_1(v_f_1150_, v_a_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adapt___boxed(lean_object* v_00_u03b5_1171_, lean_object* v_00_u03b5_x27_1172_, lean_object* v_00_u03b1_1173_, lean_object* v_f_1174_, lean_object* v_m_1175_, lean_object* v_s_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_EIO_adapt(v_00_u03b5_1171_, v_00_u03b5_x27_1172_, v_00_u03b1_1173_, v_f_1174_, v_m_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg(lean_object* v_f_1178_, lean_object* v_m_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_apply_1(v_m_1179_, lean_box(0));
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec(v_f_1178_);
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1198_; 
v_a_1190_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1192_ = v___x_1181_;
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1181_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_apply_1(v_f_1178_, v_a_1190_);
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
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg___boxed(lean_object* v_f_1199_, lean_object* v_m_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_EIO_adaptExcept___redArg(v_f_1199_, v_m_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept(lean_object* v_00_u03b5_1203_, lean_object* v_00_u03b5_x27_1204_, lean_object* v_00_u03b1_1205_, lean_object* v_f_1206_, lean_object* v_m_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_apply_1(v_m_1207_, lean_box(0));
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v_f_1206_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1226_; 
v_a_1218_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1220_ = v___x_1209_;
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1209_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_apply_1(v_f_1206_, v_a_1218_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept___boxed(lean_object* v_00_u03b5_1227_, lean_object* v_00_u03b5_x27_1228_, lean_object* v_00_u03b1_1229_, lean_object* v_f_1230_, lean_object* v_m_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_EIO_adaptExcept(v_00_u03b5_1227_, v_00_u03b5_x27_1228_, v_00_u03b1_1229_, v_f_1230_, v_m_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg(lean_object* v_act_1234_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_apply_1(v_act_1234_, lean_box(0));
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg___boxed(lean_object* v_act_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_BaseIO_toIO___redArg(v_act_1238_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO(lean_object* v_00_u03b1_1241_, lean_object* v_act_1242_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_apply_1(v_act_1242_, lean_box(0));
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_act_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_BaseIO_toIO(v_00_u03b1_1246_, v_act_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___redArg(lean_object* v_f_1250_, lean_object* v_act_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_apply_1(v_act_1251_, lean_box(0));
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v_f_1250_);
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1270_; 
v_a_1262_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1264_ = v___x_1253_;
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1253_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1266_ = lean_apply_1(v_f_1250_, v_a_1262_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1266_);
v___x_1268_ = v___x_1264_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___redArg___boxed(lean_object* v_f_1271_, lean_object* v_act_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_EIO_toIO___redArg(v_f_1271_, v_act_1272_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO(lean_object* v_00_u03b5_1275_, lean_object* v_00_u03b1_1276_, lean_object* v_f_1277_, lean_object* v_act_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_apply_1(v_act_1278_, lean_box(0));
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v_f_1277_);
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1297_; 
v_a_1289_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1291_ = v___x_1280_;
v_isShared_1292_ = v_isSharedCheck_1297_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1280_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1297_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1293_ = lean_apply_1(v_f_1277_, v_a_1289_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1293_);
v___x_1295_ = v___x_1291_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_toIO___boxed(lean_object* v_00_u03b5_1298_, lean_object* v_00_u03b1_1299_, lean_object* v_f_1300_, lean_object* v_act_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_EIO_toIO(v_00_u03b5_1298_, v_00_u03b1_1299_, v_f_1300_, v_act_1301_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg(lean_object* v_act_1304_){
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
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg___boxed(lean_object* v_act_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_EIO_toIO_x27___redArg(v_act_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27(lean_object* v_00_u03b5_1328_, lean_object* v_00_u03b1_1329_, lean_object* v_act_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_apply_1(v_act_1330_, lean_box(0));
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1341_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v_a_1333_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1337_);
v___x_1339_ = v___x_1335_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
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
v_a_1342_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1344_ = v___x_1332_;
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1332_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1350_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v_a_1342_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1346_);
v___x_1348_ = v___x_1344_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_EIO_toIO_x27___boxed(lean_object* v_00_u03b5_1351_, lean_object* v_00_u03b1_1352_, lean_object* v_act_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_EIO_toIO_x27(v_00_u03b5_1351_, v_00_u03b1_1352_, v_act_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___redArg(lean_object* v_f_1356_, lean_object* v_act_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_apply_1(v_act_1357_, lean_box(0));
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_f_1356_);
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1376_; 
v_a_1368_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1370_ = v___x_1359_;
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1359_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = lean_apply_1(v_f_1356_, v_a_1368_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1372_);
v___x_1374_ = v___x_1370_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___redArg___boxed(lean_object* v_f_1377_, lean_object* v_act_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_IO_toEIO___redArg(v_f_1377_, v_act_1378_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_IO_toEIO(lean_object* v_00_u03b5_1381_, lean_object* v_00_u03b1_1382_, lean_object* v_f_1383_, lean_object* v_act_1384_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = lean_apply_1(v_act_1384_, lean_box(0));
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_f_1383_);
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1403_; 
v_a_1395_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1397_ = v___x_1386_;
v_isShared_1398_ = v_isSharedCheck_1403_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1386_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1403_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1399_ = lean_apply_1(v_f_1383_, v_a_1395_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1399_);
v___x_1401_ = v___x_1397_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_toEIO___boxed(lean_object* v_00_u03b5_1404_, lean_object* v_00_u03b1_1405_, lean_object* v_f_1406_, lean_object* v_act_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_IO_toEIO(v_00_u03b5_1404_, v_00_u03b1_1405_, v_f_1406_, v_act_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO___redArg(lean_object* v_fn_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_apply_1(v_fn_1410_, v___x_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO(lean_object* v_00_u03b1_1413_, lean_object* v_fn_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_unsafeBaseIO___redArg(v_fn_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_unsafeEIO___redArg(lean_object* v_fn_1416_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1417_, 0, lean_box(0));
lean_closure_set(v___x_1417_, 1, lean_box(0));
lean_closure_set(v___x_1417_, 2, v_fn_1416_);
v___x_1418_ = l_unsafeBaseIO___redArg(v___x_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_unsafeEIO(lean_object* v_00_u03b5_1419_, lean_object* v_00_u03b1_1420_, lean_object* v_fn_1421_){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1422_, 0, lean_box(0));
lean_closure_set(v___x_1422_, 1, lean_box(0));
lean_closure_set(v___x_1422_, 2, v_fn_1421_);
v___x_1423_ = l_unsafeBaseIO___redArg(v___x_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_unsafeIO___redArg(lean_object* v_fn_1424_){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1425_, 0, lean_box(0));
lean_closure_set(v___x_1425_, 1, lean_box(0));
lean_closure_set(v___x_1425_, 2, v_fn_1424_);
v___x_1426_ = l_unsafeBaseIO___redArg(v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_unsafeIO(lean_object* v_00_u03b1_1427_, lean_object* v_fn_1428_){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1429_, 0, lean_box(0));
lean_closure_set(v___x_1429_, 1, lean_box(0));
lean_closure_set(v___x_1429_, 2, v_fn_1428_);
v___x_1430_ = l_unsafeBaseIO___redArg(v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_timeit___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_msg_1436_, lean_object* v_fn_1437_, lean_object* v_a_00___x40___internal___hyg_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = lean_io_timeit(v_msg_1436_, v_fn_1437_);
lean_dec_ref(v_msg_1436_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_allocprof___boxed(lean_object* v_00_u03b1_1444_, lean_object* v_msg_1445_, lean_object* v_fn_1446_, lean_object* v_a_00___x40___internal___hyg_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = lean_io_allocprof(v_msg_1445_, v_fn_1446_);
lean_dec_ref(v_msg_1445_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_IO_initializing___boxed(lean_object* v_a_00___x40___internal___hyg_1450_){
_start:
{
uint8_t v_res_1451_; lean_object* v_r_1452_; 
v_res_1451_ = lean_io_initializing();
v_r_1452_ = lean_box(v_res_1451_);
return v_r_1452_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_asTask___boxed(lean_object* v_00_u03b1_1457_, lean_object* v_act_1458_, lean_object* v_prio_1459_, lean_object* v_a_00___x40___internal___hyg_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = lean_io_as_task(v_act_1458_, v_prio_1459_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object* v_00_u03b1_1469_, lean_object* v_00_u03b2_1470_, lean_object* v_f_1471_, lean_object* v_t_1472_, lean_object* v_prio_1473_, lean_object* v_sync_1474_, lean_object* v_a_00___x40___internal___hyg_1475_){
_start:
{
uint8_t v_sync_boxed_1476_; lean_object* v_res_1477_; 
v_sync_boxed_1476_ = lean_unbox(v_sync_1474_);
v_res_1477_ = lean_io_map_task(v_f_1471_, v_t_1472_, v_prio_1473_, v_sync_boxed_1476_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object* v_00_u03b1_1485_, lean_object* v_00_u03b2_1486_, lean_object* v_t_1487_, lean_object* v_f_1488_, lean_object* v_prio_1489_, lean_object* v_sync_1490_, lean_object* v_a_00___x40___internal___hyg_1491_){
_start:
{
uint8_t v_sync_boxed_1492_; lean_object* v_res_1493_; 
v_sync_boxed_1492_ = lean_unbox(v_sync_1490_);
v_res_1493_ = lean_io_bind_task(v_t_1487_, v_f_1488_, v_prio_1489_, v_sync_boxed_1492_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg(lean_object* v_t_1494_, lean_object* v_f_1495_, lean_object* v_prio_1496_, uint8_t v_sync_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_io_map_task(v_f_1495_, v_t_1494_, v_prio_1496_, v_sync_1497_);
lean_dec_ref(v___x_1500_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg___boxed(lean_object* v_t_1501_, lean_object* v_f_1502_, lean_object* v_prio_1503_, lean_object* v_sync_1504_, lean_object* v_a_1505_){
_start:
{
uint8_t v_sync_boxed_1506_; lean_object* v_res_1507_; 
v_sync_boxed_1506_ = lean_unbox(v_sync_1504_);
v_res_1507_ = l_BaseIO_chainTask___redArg(v_t_1501_, v_f_1502_, v_prio_1503_, v_sync_boxed_1506_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask(lean_object* v_00_u03b1_1508_, lean_object* v_t_1509_, lean_object* v_f_1510_, lean_object* v_prio_1511_, uint8_t v_sync_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_BaseIO_chainTask___redArg(v_t_1509_, v_f_1510_, v_prio_1511_, v_sync_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___boxed(lean_object* v_00_u03b1_1515_, lean_object* v_t_1516_, lean_object* v_f_1517_, lean_object* v_prio_1518_, lean_object* v_sync_1519_, lean_object* v_a_1520_){
_start:
{
uint8_t v_sync_boxed_1521_; lean_object* v_res_1522_; 
v_sync_boxed_1521_ = lean_unbox(v_sync_1519_);
v_res_1522_ = l_BaseIO_chainTask(v_00_u03b1_1515_, v_t_1516_, v_f_1517_, v_prio_1518_, v_sync_boxed_1521_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(lean_object* v_x_1523_, lean_object* v_f_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1527_, 0, v_a_1525_);
lean_ctor_set(v___x_1527_, 1, v_x_1523_);
v___x_1528_ = l_List_reverse___redArg(v___x_1527_);
v___x_1529_ = lean_apply_2(v_f_1524_, v___x_1528_, lean_box(0));
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed(lean_object* v_x_1530_, lean_object* v_f_1531_, lean_object* v_a_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(v_x_1530_, v_f_1531_, v_a_1532_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed(lean_object* v_x_1535_, lean_object* v_f_1536_, lean_object* v_prio_1537_, lean_object* v_sync_1538_, lean_object* v_tail_1539_, lean_object* v_a_1540_, lean_object* v___y_1541_){
_start:
{
uint8_t v_sync_boxed_1542_; lean_object* v_res_1543_; 
v_sync_boxed_1542_ = lean_unbox(v_sync_1538_);
v_res_1543_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(v_x_1535_, v_f_1536_, v_prio_1537_, v_sync_boxed_1542_, v_tail_1539_, v_a_1540_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(lean_object* v_f_1544_, lean_object* v_prio_1545_, uint8_t v_sync_1546_, lean_object* v_x_1547_, lean_object* v_x_1548_){
_start:
{
if (lean_obj_tag(v_x_1547_) == 0)
{
if (v_sync_1546_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = l_List_reverse___redArg(v_x_1548_);
v___x_1551_ = lean_apply_1(v_f_1544_, v___x_1550_);
v___x_1552_ = lean_io_as_task(v___x_1551_, v_prio_1545_);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_dec(v_prio_1545_);
v___x_1553_ = l_List_reverse___redArg(v_x_1548_);
v___x_1554_ = lean_apply_2(v_f_1544_, v___x_1553_, lean_box(0));
v___x_1555_ = lean_task_pure(v___x_1554_);
return v___x_1555_;
}
}
else
{
lean_object* v_tail_1556_; 
v_tail_1556_ = lean_ctor_get(v_x_1547_, 1);
if (lean_obj_tag(v_tail_1556_) == 0)
{
lean_object* v_head_1557_; lean_object* v___f_1558_; lean_object* v___x_1559_; 
v_head_1557_ = lean_ctor_get(v_x_1547_, 0);
lean_inc(v_head_1557_);
lean_dec_ref_known(v_x_1547_, 2);
v___f_1558_ = lean_alloc_closure((void*)(l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1558_, 0, v_x_1548_);
lean_closure_set(v___f_1558_, 1, v_f_1544_);
v___x_1559_ = lean_io_map_task(v___f_1558_, v_head_1557_, v_prio_1545_, v_sync_1546_);
return v___x_1559_;
}
else
{
lean_object* v_head_1560_; lean_object* v___x_1561_; lean_object* v___f_1562_; lean_object* v___x_1563_; 
lean_inc(v_tail_1556_);
v_head_1560_ = lean_ctor_get(v_x_1547_, 0);
lean_inc(v_head_1560_);
lean_dec_ref_known(v_x_1547_, 2);
v___x_1561_ = lean_box(v_sync_1546_);
lean_inc(v_prio_1545_);
v___f_1562_ = lean_alloc_closure((void*)(l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1562_, 0, v_x_1548_);
lean_closure_set(v___f_1562_, 1, v_f_1544_);
lean_closure_set(v___f_1562_, 2, v_prio_1545_);
lean_closure_set(v___f_1562_, 3, v___x_1561_);
lean_closure_set(v___f_1562_, 4, v_tail_1556_);
v___x_1563_ = lean_io_bind_task(v_head_1560_, v___f_1562_, v_prio_1545_, v_sync_1546_);
return v___x_1563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(lean_object* v_x_1564_, lean_object* v_f_1565_, lean_object* v_prio_1566_, uint8_t v_sync_1567_, lean_object* v_tail_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_a_1569_);
lean_ctor_set(v___x_1571_, 1, v_x_1564_);
v___x_1572_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_1565_, v_prio_1566_, v_sync_1567_, v_tail_1568_, v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___boxed(lean_object* v_f_1573_, lean_object* v_prio_1574_, lean_object* v_sync_1575_, lean_object* v_x_1576_, lean_object* v_x_1577_, lean_object* v_a_1578_){
_start:
{
uint8_t v_sync_boxed_1579_; lean_object* v_res_1580_; 
v_sync_boxed_1579_ = lean_unbox(v_sync_1575_);
v_res_1580_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_1573_, v_prio_1574_, v_sync_boxed_1579_, v_x_1576_, v_x_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go(lean_object* v_00_u03b1_1581_, lean_object* v_00_u03b2_1582_, lean_object* v_f_1583_, lean_object* v_prio_1584_, uint8_t v_sync_1585_, lean_object* v_x_1586_, lean_object* v_x_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_1583_, v_prio_1584_, v_sync_1585_, v_x_1586_, v_x_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___boxed(lean_object* v_00_u03b1_1590_, lean_object* v_00_u03b2_1591_, lean_object* v_f_1592_, lean_object* v_prio_1593_, lean_object* v_sync_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_, lean_object* v_a_1597_){
_start:
{
uint8_t v_sync_boxed_1598_; lean_object* v_res_1599_; 
v_sync_boxed_1598_ = lean_unbox(v_sync_1594_);
v_res_1599_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go(v_00_u03b1_1590_, v_00_u03b2_1591_, v_f_1592_, v_prio_1593_, v_sync_boxed_1598_, v_x_1595_, v_x_1596_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg(lean_object* v_f_1600_, lean_object* v_tasks_1601_, lean_object* v_prio_1602_, uint8_t v_sync_1603_){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_box(0);
v___x_1606_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_1600_, v_prio_1602_, v_sync_1603_, v_tasks_1601_, v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg___boxed(lean_object* v_f_1607_, lean_object* v_tasks_1608_, lean_object* v_prio_1609_, lean_object* v_sync_1610_, lean_object* v_a_1611_){
_start:
{
uint8_t v_sync_boxed_1612_; lean_object* v_res_1613_; 
v_sync_boxed_1612_ = lean_unbox(v_sync_1610_);
v_res_1613_ = l_BaseIO_mapTasks___redArg(v_f_1607_, v_tasks_1608_, v_prio_1609_, v_sync_boxed_1612_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks(lean_object* v_00_u03b1_1614_, lean_object* v_00_u03b2_1615_, lean_object* v_f_1616_, lean_object* v_tasks_1617_, lean_object* v_prio_1618_, uint8_t v_sync_1619_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_BaseIO_mapTasks___redArg(v_f_1616_, v_tasks_1617_, v_prio_1618_, v_sync_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___boxed(lean_object* v_00_u03b1_1622_, lean_object* v_00_u03b2_1623_, lean_object* v_f_1624_, lean_object* v_tasks_1625_, lean_object* v_prio_1626_, lean_object* v_sync_1627_, lean_object* v_a_1628_){
_start:
{
uint8_t v_sync_boxed_1629_; lean_object* v_res_1630_; 
v_sync_boxed_1629_ = lean_unbox(v_sync_1627_);
v_res_1630_ = l_BaseIO_mapTasks(v_00_u03b1_1622_, v_00_u03b2_1623_, v_f_1624_, v_tasks_1625_, v_prio_1626_, v_sync_boxed_1629_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___redArg(lean_object* v_act_1631_, lean_object* v_prio_1632_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1634_, 0, lean_box(0));
lean_closure_set(v___x_1634_, 1, lean_box(0));
lean_closure_set(v___x_1634_, 2, v_act_1631_);
v___x_1635_ = lean_io_as_task(v___x_1634_, v_prio_1632_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___redArg___boxed(lean_object* v_act_1636_, lean_object* v_prio_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_EIO_asTask___redArg(v_act_1636_, v_prio_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask(lean_object* v_00_u03b5_1640_, lean_object* v_00_u03b1_1641_, lean_object* v_act_1642_, lean_object* v_prio_1643_){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1645_, 0, lean_box(0));
lean_closure_set(v___x_1645_, 1, lean_box(0));
lean_closure_set(v___x_1645_, 2, v_act_1642_);
v___x_1646_ = lean_io_as_task(v___x_1645_, v_prio_1643_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_EIO_asTask___boxed(lean_object* v_00_u03b5_1647_, lean_object* v_00_u03b1_1648_, lean_object* v_act_1649_, lean_object* v_prio_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_EIO_asTask(v_00_u03b5_1647_, v_00_u03b1_1648_, v_act_1649_, v_prio_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0(lean_object* v_f_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_apply_2(v_f_1653_, v_a_1654_, lean_box(0));
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 1);
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_a_1665_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1656_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1656_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 0);
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0___boxed(lean_object* v_f_1673_, lean_object* v_a_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_EIO_mapTask___redArg___lam__0(v_f_1673_, v_a_1674_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg(lean_object* v_f_1677_, lean_object* v_t_1678_, lean_object* v_prio_1679_, uint8_t v_sync_1680_){
_start:
{
lean_object* v___f_1682_; lean_object* v___x_1683_; 
v___f_1682_ = lean_alloc_closure((void*)(l_EIO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1682_, 0, v_f_1677_);
v___x_1683_ = lean_io_map_task(v___f_1682_, v_t_1678_, v_prio_1679_, v_sync_1680_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___boxed(lean_object* v_f_1684_, lean_object* v_t_1685_, lean_object* v_prio_1686_, lean_object* v_sync_1687_, lean_object* v_a_1688_){
_start:
{
uint8_t v_sync_boxed_1689_; lean_object* v_res_1690_; 
v_sync_boxed_1689_ = lean_unbox(v_sync_1687_);
v_res_1690_ = l_EIO_mapTask___redArg(v_f_1684_, v_t_1685_, v_prio_1686_, v_sync_boxed_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask(lean_object* v_00_u03b1_1691_, lean_object* v_00_u03b5_1692_, lean_object* v_00_u03b2_1693_, lean_object* v_f_1694_, lean_object* v_t_1695_, lean_object* v_prio_1696_, uint8_t v_sync_1697_){
_start:
{
lean_object* v___f_1699_; lean_object* v___x_1700_; 
v___f_1699_ = lean_alloc_closure((void*)(l_EIO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1699_, 0, v_f_1694_);
v___x_1700_ = lean_io_map_task(v___f_1699_, v_t_1695_, v_prio_1696_, v_sync_1697_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTask___boxed(lean_object* v_00_u03b1_1701_, lean_object* v_00_u03b5_1702_, lean_object* v_00_u03b2_1703_, lean_object* v_f_1704_, lean_object* v_t_1705_, lean_object* v_prio_1706_, lean_object* v_sync_1707_, lean_object* v_a_1708_){
_start:
{
uint8_t v_sync_boxed_1709_; lean_object* v_res_1710_; 
v_sync_boxed_1709_ = lean_unbox(v_sync_1707_);
v_res_1710_ = l_EIO_mapTask(v_00_u03b1_1701_, v_00_u03b5_1702_, v_00_u03b2_1703_, v_f_1704_, v_t_1705_, v_prio_1706_, v_sync_boxed_1709_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0(lean_object* v_f_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_apply_2(v_f_1711_, v_a_1712_, lean_box(0));
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1714_, 1);
return v_a_1715_;
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1724_; 
v_a_1716_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1718_ = v___x_1714_;
v_isShared_1719_ = v_isSharedCheck_1724_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1714_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1724_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
lean_ctor_set_tag(v___x_1718_, 0);
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_task_pure(v___x_1721_);
return v___x_1722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0___boxed(lean_object* v_f_1725_, lean_object* v_a_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_EIO_bindTask___redArg___lam__0(v_f_1725_, v_a_1726_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg(lean_object* v_t_1729_, lean_object* v_f_1730_, lean_object* v_prio_1731_, uint8_t v_sync_1732_){
_start:
{
lean_object* v___f_1734_; lean_object* v___x_1735_; 
v___f_1734_ = lean_alloc_closure((void*)(l_EIO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1734_, 0, v_f_1730_);
v___x_1735_ = lean_io_bind_task(v_t_1729_, v___f_1734_, v_prio_1731_, v_sync_1732_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___boxed(lean_object* v_t_1736_, lean_object* v_f_1737_, lean_object* v_prio_1738_, lean_object* v_sync_1739_, lean_object* v_a_1740_){
_start:
{
uint8_t v_sync_boxed_1741_; lean_object* v_res_1742_; 
v_sync_boxed_1741_ = lean_unbox(v_sync_1739_);
v_res_1742_ = l_EIO_bindTask___redArg(v_t_1736_, v_f_1737_, v_prio_1738_, v_sync_boxed_1741_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask(lean_object* v_00_u03b1_1743_, lean_object* v_00_u03b5_1744_, lean_object* v_00_u03b2_1745_, lean_object* v_t_1746_, lean_object* v_f_1747_, lean_object* v_prio_1748_, uint8_t v_sync_1749_){
_start:
{
lean_object* v___f_1751_; lean_object* v___x_1752_; 
v___f_1751_ = lean_alloc_closure((void*)(l_EIO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1751_, 0, v_f_1747_);
v___x_1752_ = lean_io_bind_task(v_t_1746_, v___f_1751_, v_prio_1748_, v_sync_1749_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_EIO_bindTask___boxed(lean_object* v_00_u03b1_1753_, lean_object* v_00_u03b5_1754_, lean_object* v_00_u03b2_1755_, lean_object* v_t_1756_, lean_object* v_f_1757_, lean_object* v_prio_1758_, lean_object* v_sync_1759_, lean_object* v_a_1760_){
_start:
{
uint8_t v_sync_boxed_1761_; lean_object* v_res_1762_; 
v_sync_boxed_1761_ = lean_unbox(v_sync_1759_);
v_res_1762_ = l_EIO_bindTask(v_00_u03b1_1753_, v_00_u03b5_1754_, v_00_u03b2_1755_, v_t_1756_, v_f_1757_, v_prio_1758_, v_sync_boxed_1761_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0(lean_object* v_f_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_apply_2(v_f_1763_, v_a_1764_, lean_box(0));
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set_tag(v___x_1769_, 1);
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
v_a_1775_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1766_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1766_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set_tag(v___x_1777_, 0);
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0___boxed(lean_object* v_f_1783_, lean_object* v_a_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_EIO_chainTask___redArg___lam__0(v_f_1783_, v_a_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg(lean_object* v_t_1787_, lean_object* v_f_1788_, lean_object* v_prio_1789_, uint8_t v_sync_1790_){
_start:
{
lean_object* v___f_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___f_1792_ = lean_alloc_closure((void*)(l_EIO_chainTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1792_, 0, v_f_1788_);
v___x_1793_ = lean_box(0);
v___x_1794_ = lean_io_map_task(v___f_1792_, v_t_1787_, v_prio_1789_, v_sync_1790_);
lean_dec_ref(v___x_1794_);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___boxed(lean_object* v_t_1796_, lean_object* v_f_1797_, lean_object* v_prio_1798_, lean_object* v_sync_1799_, lean_object* v_a_1800_){
_start:
{
uint8_t v_sync_boxed_1801_; lean_object* v_res_1802_; 
v_sync_boxed_1801_ = lean_unbox(v_sync_1799_);
v_res_1802_ = l_EIO_chainTask___redArg(v_t_1796_, v_f_1797_, v_prio_1798_, v_sync_boxed_1801_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask(lean_object* v_00_u03b1_1803_, lean_object* v_00_u03b5_1804_, lean_object* v_t_1805_, lean_object* v_f_1806_, lean_object* v_prio_1807_, uint8_t v_sync_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_EIO_chainTask___redArg(v_t_1805_, v_f_1806_, v_prio_1807_, v_sync_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_EIO_chainTask___boxed(lean_object* v_00_u03b1_1811_, lean_object* v_00_u03b5_1812_, lean_object* v_t_1813_, lean_object* v_f_1814_, lean_object* v_prio_1815_, lean_object* v_sync_1816_, lean_object* v_a_1817_){
_start:
{
uint8_t v_sync_boxed_1818_; lean_object* v_res_1819_; 
v_sync_boxed_1818_ = lean_unbox(v_sync_1816_);
v_res_1819_ = l_EIO_chainTask(v_00_u03b1_1811_, v_00_u03b5_1812_, v_t_1813_, v_f_1814_, v_prio_1815_, v_sync_boxed_1818_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0(lean_object* v_f_1820_, lean_object* v_as_1821_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_apply_2(v_f_1820_, v_as_1821_, lean_box(0));
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set_tag(v___x_1826_, 1);
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
v_a_1832_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1823_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1823_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set_tag(v___x_1834_, 0);
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0___boxed(lean_object* v_f_1840_, lean_object* v_as_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_EIO_mapTasks___redArg___lam__0(v_f_1840_, v_as_1841_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg(lean_object* v_f_1844_, lean_object* v_tasks_1845_, lean_object* v_prio_1846_, uint8_t v_sync_1847_){
_start:
{
lean_object* v___f_1849_; lean_object* v___x_1850_; 
v___f_1849_ = lean_alloc_closure((void*)(l_EIO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1849_, 0, v_f_1844_);
v___x_1850_ = l_BaseIO_mapTasks___redArg(v___f_1849_, v_tasks_1845_, v_prio_1846_, v_sync_1847_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___boxed(lean_object* v_f_1851_, lean_object* v_tasks_1852_, lean_object* v_prio_1853_, lean_object* v_sync_1854_, lean_object* v_a_1855_){
_start:
{
uint8_t v_sync_boxed_1856_; lean_object* v_res_1857_; 
v_sync_boxed_1856_ = lean_unbox(v_sync_1854_);
v_res_1857_ = l_EIO_mapTasks___redArg(v_f_1851_, v_tasks_1852_, v_prio_1853_, v_sync_boxed_1856_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks(lean_object* v_00_u03b1_1858_, lean_object* v_00_u03b5_1859_, lean_object* v_00_u03b2_1860_, lean_object* v_f_1861_, lean_object* v_tasks_1862_, lean_object* v_prio_1863_, uint8_t v_sync_1864_){
_start:
{
lean_object* v___f_1866_; lean_object* v___x_1867_; 
v___f_1866_ = lean_alloc_closure((void*)(l_EIO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1866_, 0, v_f_1861_);
v___x_1867_ = l_BaseIO_mapTasks___redArg(v___f_1866_, v_tasks_1862_, v_prio_1863_, v_sync_1864_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___boxed(lean_object* v_00_u03b1_1868_, lean_object* v_00_u03b5_1869_, lean_object* v_00_u03b2_1870_, lean_object* v_f_1871_, lean_object* v_tasks_1872_, lean_object* v_prio_1873_, lean_object* v_sync_1874_, lean_object* v_a_1875_){
_start:
{
uint8_t v_sync_boxed_1876_; lean_object* v_res_1877_; 
v_sync_boxed_1876_ = lean_unbox(v_sync_1874_);
v_res_1877_ = l_EIO_mapTasks(v_00_u03b1_1868_, v_00_u03b5_1869_, v_00_u03b2_1870_, v_f_1871_, v_tasks_1872_, v_prio_1873_, v_sync_boxed_1876_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg(lean_object* v_inst_1878_, lean_object* v_e_1879_){
_start:
{
if (lean_obj_tag(v_e_1879_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1890_; 
v_a_1881_ = lean_ctor_get(v_e_1879_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_e_1879_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1883_ = v_e_1879_;
v_isShared_1884_ = v_isSharedCheck_1890_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v_e_1879_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1890_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1885_ = lean_apply_1(v_inst_1878_, v_a_1881_);
v___x_1886_ = lean_mk_io_user_error(v___x_1885_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set_tag(v___x_1883_, 1);
lean_ctor_set(v___x_1883_, 0, v___x_1886_);
v___x_1888_ = v___x_1883_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec_ref(v_inst_1878_);
v_a_1891_ = lean_ctor_get(v_e_1879_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_e_1879_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v_e_1879_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v_e_1879_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set_tag(v___x_1893_, 0);
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg___boxed(lean_object* v_inst_1899_, lean_object* v_e_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_IO_ofExcept___redArg(v_inst_1899_, v_e_1900_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept(lean_object* v_00_u03b5_1903_, lean_object* v_00_u03b1_1904_, lean_object* v_inst_1905_, lean_object* v_e_1906_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_IO_ofExcept___redArg(v_inst_1905_, v_e_1906_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___boxed(lean_object* v_00_u03b5_1909_, lean_object* v_00_u03b1_1910_, lean_object* v_inst_1911_, lean_object* v_e_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_IO_ofExcept(v_00_u03b5_1909_, v_00_u03b1_1910_, v_inst_1911_, v_e_1912_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg(lean_object* v_fn_1915_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_box(0);
v___x_1918_ = lean_apply_1(v_fn_1915_, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg___boxed(lean_object* v_fn_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_IO_lazyPure___redArg(v_fn_1920_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure(lean_object* v_00_u03b1_1923_, lean_object* v_fn_1924_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_IO_lazyPure___redArg(v_fn_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_IO_lazyPure___boxed(lean_object* v_00_u03b1_1927_, lean_object* v_fn_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_IO_lazyPure(v_00_u03b1_1927_, v_fn_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_IO_monoMsNow___boxed(lean_object* v_a_00___x40___internal___hyg_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = lean_io_mono_ms_now();
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_IO_monoNanosNow___boxed(lean_object* v_a_00___x40___internal___hyg_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = lean_io_mono_nanos_now();
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_IO_getRandomBytes___boxed(lean_object* v_nBytes_1939_, lean_object* v_a_00___x40___internal___hyg_1940_){
_start:
{
size_t v_nBytes_boxed_1941_; lean_object* v_res_1942_; 
v_nBytes_boxed_1941_ = lean_unbox_usize(v_nBytes_1939_);
lean_dec(v_nBytes_1939_);
v_res_1942_ = lean_io_get_random_bytes(v_nBytes_boxed_1941_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___lam__0(lean_object* v_x_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_box(0);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___lam__0___boxed(lean_object* v_s_1946_, lean_object* v_x_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_IO_sleep___lam__0(v_x_1947_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_IO_sleep(uint32_t v_ms_1949_){
_start:
{
lean_object* v___f_1951_; lean_object* v___x_1952_; 
v___f_1951_ = lean_alloc_closure((void*)(l_IO_sleep___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1951_, 0, lean_box(0));
v___x_1952_ = lean_dbg_sleep(v_ms_1949_, v___f_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_IO_sleep___boxed(lean_object* v_ms_1953_, lean_object* v_s_1954_){
_start:
{
uint32_t v_ms_boxed_1955_; lean_object* v_res_1956_; 
v_ms_boxed_1955_ = lean_unbox_uint32(v_ms_1953_);
lean_dec(v_ms_1953_);
v_res_1956_ = l_IO_sleep(v_ms_boxed_1955_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___redArg(lean_object* v_act_1957_, lean_object* v_prio_1958_){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1960_, 0, lean_box(0));
lean_closure_set(v___x_1960_, 1, lean_box(0));
lean_closure_set(v___x_1960_, 2, v_act_1957_);
v___x_1961_ = lean_io_as_task(v___x_1960_, v_prio_1958_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___redArg___boxed(lean_object* v_act_1962_, lean_object* v_prio_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_IO_asTask___redArg(v_act_1962_, v_prio_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_IO_asTask(lean_object* v_00_u03b1_1966_, lean_object* v_act_1967_, lean_object* v_prio_1968_){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1970_, 0, lean_box(0));
lean_closure_set(v___x_1970_, 1, lean_box(0));
lean_closure_set(v___x_1970_, 2, v_act_1967_);
v___x_1971_ = lean_io_as_task(v___x_1970_, v_prio_1968_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_IO_asTask___boxed(lean_object* v_00_u03b1_1972_, lean_object* v_act_1973_, lean_object* v_prio_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_IO_asTask(v_00_u03b1_1972_, v_act_1973_, v_prio_1974_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0(lean_object* v_f_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_apply_2(v_f_1977_, v_a_1978_, lean_box(0));
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 1);
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
v_a_1989_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1980_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1980_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set_tag(v___x_1991_, 0);
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0___boxed(lean_object* v_f_1997_, lean_object* v_a_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_IO_mapTask___redArg___lam__0(v_f_1997_, v_a_1998_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg(lean_object* v_f_2001_, lean_object* v_t_2002_, lean_object* v_prio_2003_, uint8_t v_sync_2004_){
_start:
{
lean_object* v___f_2006_; lean_object* v___x_2007_; 
v___f_2006_ = lean_alloc_closure((void*)(l_IO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2006_, 0, v_f_2001_);
v___x_2007_ = lean_io_map_task(v___f_2006_, v_t_2002_, v_prio_2003_, v_sync_2004_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___boxed(lean_object* v_f_2008_, lean_object* v_t_2009_, lean_object* v_prio_2010_, lean_object* v_sync_2011_, lean_object* v_a_2012_){
_start:
{
uint8_t v_sync_boxed_2013_; lean_object* v_res_2014_; 
v_sync_boxed_2013_ = lean_unbox(v_sync_2011_);
v_res_2014_ = l_IO_mapTask___redArg(v_f_2008_, v_t_2009_, v_prio_2010_, v_sync_boxed_2013_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask(lean_object* v_00_u03b1_2015_, lean_object* v_00_u03b2_2016_, lean_object* v_f_2017_, lean_object* v_t_2018_, lean_object* v_prio_2019_, uint8_t v_sync_2020_){
_start:
{
lean_object* v___f_2022_; lean_object* v___x_2023_; 
v___f_2022_ = lean_alloc_closure((void*)(l_IO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2022_, 0, v_f_2017_);
v___x_2023_ = lean_io_map_task(v___f_2022_, v_t_2018_, v_prio_2019_, v_sync_2020_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTask___boxed(lean_object* v_00_u03b1_2024_, lean_object* v_00_u03b2_2025_, lean_object* v_f_2026_, lean_object* v_t_2027_, lean_object* v_prio_2028_, lean_object* v_sync_2029_, lean_object* v_a_2030_){
_start:
{
uint8_t v_sync_boxed_2031_; lean_object* v_res_2032_; 
v_sync_boxed_2031_ = lean_unbox(v_sync_2029_);
v_res_2032_ = l_IO_mapTask(v_00_u03b1_2024_, v_00_u03b2_2025_, v_f_2026_, v_t_2027_, v_prio_2028_, v_sync_boxed_2031_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0(lean_object* v_f_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_apply_2(v_f_2033_, v_a_2034_, lean_box(0));
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
return v_a_2037_;
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2046_; 
v_a_2038_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2040_ = v___x_2036_;
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2036_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 0);
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; 
v___x_2044_ = lean_task_pure(v___x_2043_);
return v___x_2044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0___boxed(lean_object* v_f_2047_, lean_object* v_a_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_IO_bindTask___redArg___lam__0(v_f_2047_, v_a_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg(lean_object* v_t_2051_, lean_object* v_f_2052_, lean_object* v_prio_2053_, uint8_t v_sync_2054_){
_start:
{
lean_object* v___f_2056_; lean_object* v___x_2057_; 
v___f_2056_ = lean_alloc_closure((void*)(l_IO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2056_, 0, v_f_2052_);
v___x_2057_ = lean_io_bind_task(v_t_2051_, v___f_2056_, v_prio_2053_, v_sync_2054_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___boxed(lean_object* v_t_2058_, lean_object* v_f_2059_, lean_object* v_prio_2060_, lean_object* v_sync_2061_, lean_object* v_a_2062_){
_start:
{
uint8_t v_sync_boxed_2063_; lean_object* v_res_2064_; 
v_sync_boxed_2063_ = lean_unbox(v_sync_2061_);
v_res_2064_ = l_IO_bindTask___redArg(v_t_2058_, v_f_2059_, v_prio_2060_, v_sync_boxed_2063_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask(lean_object* v_00_u03b1_2065_, lean_object* v_00_u03b2_2066_, lean_object* v_t_2067_, lean_object* v_f_2068_, lean_object* v_prio_2069_, uint8_t v_sync_2070_){
_start:
{
lean_object* v___f_2072_; lean_object* v___x_2073_; 
v___f_2072_ = lean_alloc_closure((void*)(l_IO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2072_, 0, v_f_2068_);
v___x_2073_ = lean_io_bind_task(v_t_2067_, v___f_2072_, v_prio_2069_, v_sync_2070_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_IO_bindTask___boxed(lean_object* v_00_u03b1_2074_, lean_object* v_00_u03b2_2075_, lean_object* v_t_2076_, lean_object* v_f_2077_, lean_object* v_prio_2078_, lean_object* v_sync_2079_, lean_object* v_a_2080_){
_start:
{
uint8_t v_sync_boxed_2081_; lean_object* v_res_2082_; 
v_sync_boxed_2081_ = lean_unbox(v_sync_2079_);
v_res_2082_ = l_IO_bindTask(v_00_u03b1_2074_, v_00_u03b2_2075_, v_t_2076_, v_f_2077_, v_prio_2078_, v_sync_boxed_2081_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___redArg(lean_object* v_t_2083_, lean_object* v_f_2084_, lean_object* v_prio_2085_, uint8_t v_sync_2086_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_EIO_chainTask___redArg(v_t_2083_, v_f_2084_, v_prio_2085_, v_sync_2086_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___redArg___boxed(lean_object* v_t_2089_, lean_object* v_f_2090_, lean_object* v_prio_2091_, lean_object* v_sync_2092_, lean_object* v_a_2093_){
_start:
{
uint8_t v_sync_boxed_2094_; lean_object* v_res_2095_; 
v_sync_boxed_2094_ = lean_unbox(v_sync_2092_);
v_res_2095_ = l_IO_chainTask___redArg(v_t_2089_, v_f_2090_, v_prio_2091_, v_sync_boxed_2094_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask(lean_object* v_00_u03b1_2096_, lean_object* v_t_2097_, lean_object* v_f_2098_, lean_object* v_prio_2099_, uint8_t v_sync_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_EIO_chainTask___redArg(v_t_2097_, v_f_2098_, v_prio_2099_, v_sync_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_IO_chainTask___boxed(lean_object* v_00_u03b1_2103_, lean_object* v_t_2104_, lean_object* v_f_2105_, lean_object* v_prio_2106_, lean_object* v_sync_2107_, lean_object* v_a_2108_){
_start:
{
uint8_t v_sync_boxed_2109_; lean_object* v_res_2110_; 
v_sync_boxed_2109_ = lean_unbox(v_sync_2107_);
v_res_2110_ = l_IO_chainTask(v_00_u03b1_2103_, v_t_2104_, v_f_2105_, v_prio_2106_, v_sync_boxed_2109_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0(lean_object* v_f_2111_, lean_object* v_as_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_apply_2(v_f_2111_, v_as_2112_, lean_box(0));
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
lean_ctor_set_tag(v___x_2117_, 1);
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
v_a_2123_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2114_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2114_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set_tag(v___x_2125_, 0);
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0___boxed(lean_object* v_f_2131_, lean_object* v_as_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_IO_mapTasks___redArg___lam__0(v_f_2131_, v_as_2132_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg(lean_object* v_f_2135_, lean_object* v_tasks_2136_, lean_object* v_prio_2137_, uint8_t v_sync_2138_){
_start:
{
lean_object* v___f_2140_; lean_object* v___x_2141_; 
v___f_2140_ = lean_alloc_closure((void*)(l_IO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2140_, 0, v_f_2135_);
v___x_2141_ = l_BaseIO_mapTasks___redArg(v___f_2140_, v_tasks_2136_, v_prio_2137_, v_sync_2138_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___boxed(lean_object* v_f_2142_, lean_object* v_tasks_2143_, lean_object* v_prio_2144_, lean_object* v_sync_2145_, lean_object* v_a_2146_){
_start:
{
uint8_t v_sync_boxed_2147_; lean_object* v_res_2148_; 
v_sync_boxed_2147_ = lean_unbox(v_sync_2145_);
v_res_2148_ = l_IO_mapTasks___redArg(v_f_2142_, v_tasks_2143_, v_prio_2144_, v_sync_boxed_2147_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks(lean_object* v_00_u03b1_2149_, lean_object* v_00_u03b2_2150_, lean_object* v_f_2151_, lean_object* v_tasks_2152_, lean_object* v_prio_2153_, uint8_t v_sync_2154_){
_start:
{
lean_object* v___f_2156_; lean_object* v___x_2157_; 
v___f_2156_ = lean_alloc_closure((void*)(l_IO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2156_, 0, v_f_2151_);
v___x_2157_ = l_BaseIO_mapTasks___redArg(v___f_2156_, v_tasks_2152_, v_prio_2153_, v_sync_2154_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_IO_mapTasks___boxed(lean_object* v_00_u03b1_2158_, lean_object* v_00_u03b2_2159_, lean_object* v_f_2160_, lean_object* v_tasks_2161_, lean_object* v_prio_2162_, lean_object* v_sync_2163_, lean_object* v_a_2164_){
_start:
{
uint8_t v_sync_boxed_2165_; lean_object* v_res_2166_; 
v_sync_boxed_2165_ = lean_unbox(v_sync_2163_);
v_res_2166_ = l_IO_mapTasks(v_00_u03b1_2158_, v_00_u03b2_2159_, v_f_2160_, v_tasks_2161_, v_prio_2162_, v_sync_boxed_2165_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_IO_checkCanceled___boxed(lean_object* v_a_00___x40___internal___hyg_2168_){
_start:
{
uint8_t v_res_2169_; lean_object* v_r_2170_; 
v_res_2169_ = lean_io_check_canceled();
v_r_2170_ = lean_box(v_res_2169_);
return v_r_2170_;
}
}
LEAN_EXPORT lean_object* l_IO_cancel___boxed(lean_object* v_00_u03b1_2174_, lean_object* v_a_00___x40___internal___hyg_2175_, lean_object* v_a_00___x40___internal___hyg_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = lean_io_cancel(v_a_00___x40___internal___hyg_2175_);
lean_dec_ref(v_a_00___x40___internal___hyg_2175_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx___impl(uint8_t v_x_2178_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_box(v_x_2178_);
v___x_2180_ = lean_obj_tag_nat(v___x_2179_);
lean_dec(v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx___impl___boxed(lean_object* v_x_2181_){
_start:
{
uint8_t v_x_4__boxed_2182_; lean_object* v_res_2183_; 
v_x_4__boxed_2182_ = lean_unbox(v_x_2181_);
v_res_2183_ = l_IO_TaskState_ctorIdx___impl(v_x_4__boxed_2182_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg(lean_object* v_k_2184_){
_start:
{
lean_inc(v_k_2184_);
return v_k_2184_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg___boxed(lean_object* v_k_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_IO_TaskState_ctorElim___redArg(v_k_2185_);
lean_dec(v_k_2185_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim(lean_object* v_motive_2187_, lean_object* v_ctorIdx_2188_, uint8_t v_t_2189_, lean_object* v_h_2190_, lean_object* v_k_2191_){
_start:
{
lean_inc(v_k_2191_);
return v_k_2191_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___boxed(lean_object* v_motive_2192_, lean_object* v_ctorIdx_2193_, lean_object* v_t_2194_, lean_object* v_h_2195_, lean_object* v_k_2196_){
_start:
{
uint8_t v_t_boxed_2197_; lean_object* v_res_2198_; 
v_t_boxed_2197_ = lean_unbox(v_t_2194_);
v_res_2198_ = l_IO_TaskState_ctorElim(v_motive_2192_, v_ctorIdx_2193_, v_t_boxed_2197_, v_h_2195_, v_k_2196_);
lean_dec(v_k_2196_);
lean_dec(v_ctorIdx_2193_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg(lean_object* v_waiting_2199_){
_start:
{
lean_inc(v_waiting_2199_);
return v_waiting_2199_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg___boxed(lean_object* v_waiting_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_IO_TaskState_waiting_elim___redArg(v_waiting_2200_);
lean_dec(v_waiting_2200_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim(lean_object* v_motive_2202_, uint8_t v_t_2203_, lean_object* v_h_2204_, lean_object* v_waiting_2205_){
_start:
{
lean_inc(v_waiting_2205_);
return v_waiting_2205_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___boxed(lean_object* v_motive_2206_, lean_object* v_t_2207_, lean_object* v_h_2208_, lean_object* v_waiting_2209_){
_start:
{
uint8_t v_t_boxed_2210_; lean_object* v_res_2211_; 
v_t_boxed_2210_ = lean_unbox(v_t_2207_);
v_res_2211_ = l_IO_TaskState_waiting_elim(v_motive_2206_, v_t_boxed_2210_, v_h_2208_, v_waiting_2209_);
lean_dec(v_waiting_2209_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg(lean_object* v_running_2212_){
_start:
{
lean_inc(v_running_2212_);
return v_running_2212_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg___boxed(lean_object* v_running_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_IO_TaskState_running_elim___redArg(v_running_2213_);
lean_dec(v_running_2213_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim(lean_object* v_motive_2215_, uint8_t v_t_2216_, lean_object* v_h_2217_, lean_object* v_running_2218_){
_start:
{
lean_inc(v_running_2218_);
return v_running_2218_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___boxed(lean_object* v_motive_2219_, lean_object* v_t_2220_, lean_object* v_h_2221_, lean_object* v_running_2222_){
_start:
{
uint8_t v_t_boxed_2223_; lean_object* v_res_2224_; 
v_t_boxed_2223_ = lean_unbox(v_t_2220_);
v_res_2224_ = l_IO_TaskState_running_elim(v_motive_2219_, v_t_boxed_2223_, v_h_2221_, v_running_2222_);
lean_dec(v_running_2222_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg(lean_object* v_finished_2225_){
_start:
{
lean_inc(v_finished_2225_);
return v_finished_2225_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg___boxed(lean_object* v_finished_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_IO_TaskState_finished_elim___redArg(v_finished_2226_);
lean_dec(v_finished_2226_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim(lean_object* v_motive_2228_, uint8_t v_t_2229_, lean_object* v_h_2230_, lean_object* v_finished_2231_){
_start:
{
lean_inc(v_finished_2231_);
return v_finished_2231_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___boxed(lean_object* v_motive_2232_, lean_object* v_t_2233_, lean_object* v_h_2234_, lean_object* v_finished_2235_){
_start:
{
uint8_t v_t_boxed_2236_; lean_object* v_res_2237_; 
v_t_boxed_2236_ = lean_unbox(v_t_2233_);
v_res_2237_ = l_IO_TaskState_finished_elim(v_motive_2232_, v_t_boxed_2236_, v_h_2234_, v_finished_2235_);
lean_dec(v_finished_2235_);
return v_res_2237_;
}
}
static uint8_t _init_l_IO_instInhabitedTaskState_default(void){
_start:
{
uint8_t v___x_2238_; 
v___x_2238_ = 0;
return v___x_2238_;
}
}
static uint8_t _init_l_IO_instInhabitedTaskState(void){
_start:
{
uint8_t v___x_2239_; 
v___x_2239_ = 0;
return v___x_2239_;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__6(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = lean_unsigned_to_nat(2u);
v___x_2250_ = lean_nat_to_int(v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__7(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_unsigned_to_nat(1u);
v___x_2252_ = lean_nat_to_int(v___x_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr(uint8_t v_x_2253_, lean_object* v_prec_2254_){
_start:
{
lean_object* v___y_2256_; lean_object* v___y_2263_; lean_object* v___y_2270_; 
switch(v_x_2253_)
{
case 0:
{
lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2276_ = lean_unsigned_to_nat(1024u);
v___x_2277_ = lean_nat_dec_le(v___x_2276_, v_prec_2254_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2256_ = v___x_2278_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2256_ = v___x_2279_;
goto v___jp_2255_;
}
}
case 1:
{
lean_object* v___x_2280_; uint8_t v___x_2281_; 
v___x_2280_ = lean_unsigned_to_nat(1024u);
v___x_2281_ = lean_nat_dec_le(v___x_2280_, v_prec_2254_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; 
v___x_2282_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2263_ = v___x_2282_;
goto v___jp_2262_;
}
else
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2263_ = v___x_2283_;
goto v___jp_2262_;
}
}
default: 
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = lean_unsigned_to_nat(1024u);
v___x_2285_ = lean_nat_dec_le(v___x_2284_, v_prec_2254_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; 
v___x_2286_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2270_ = v___x_2286_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2270_ = v___x_2287_;
goto v___jp_2269_;
}
}
}
v___jp_2255_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2257_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__1));
lean_inc(v___y_2256_);
v___x_2258_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___y_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = 0;
v___x_2260_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set_uint8(v___x_2260_, sizeof(void*)*1, v___x_2259_);
v___x_2261_ = l_Repr_addAppParen(v___x_2260_, v_prec_2254_);
return v___x_2261_;
}
v___jp_2262_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2264_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__3));
lean_inc(v___y_2263_);
v___x_2265_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___y_2263_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
v___x_2266_ = 0;
v___x_2267_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2267_, 0, v___x_2265_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*1, v___x_2266_);
v___x_2268_ = l_Repr_addAppParen(v___x_2267_, v_prec_2254_);
return v___x_2268_;
}
v___jp_2269_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2271_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__5));
lean_inc(v___y_2270_);
v___x_2272_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___y_2270_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = 0;
v___x_2274_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set_uint8(v___x_2274_, sizeof(void*)*1, v___x_2273_);
v___x_2275_ = l_Repr_addAppParen(v___x_2274_, v_prec_2254_);
return v___x_2275_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr___boxed(lean_object* v_x_2288_, lean_object* v_prec_2289_){
_start:
{
uint8_t v_x_171__boxed_2290_; lean_object* v_res_2291_; 
v_x_171__boxed_2290_ = lean_unbox(v_x_2288_);
v_res_2291_ = l_IO_instReprTaskState_repr(v_x_171__boxed_2290_, v_prec_2289_);
lean_dec(v_prec_2289_);
return v_res_2291_;
}
}
LEAN_EXPORT uint8_t l_IO_TaskState_ofNat(lean_object* v_n_2294_){
_start:
{
lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2295_ = lean_unsigned_to_nat(0u);
v___x_2296_ = lean_nat_dec_le(v_n_2294_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; uint8_t v___x_2298_; 
v___x_2297_ = lean_unsigned_to_nat(1u);
v___x_2298_ = lean_nat_dec_le(v_n_2294_, v___x_2297_);
if (v___x_2298_ == 0)
{
uint8_t v___x_2299_; 
v___x_2299_ = 2;
return v___x_2299_;
}
else
{
uint8_t v___x_2300_; 
v___x_2300_ = 1;
return v___x_2300_;
}
}
else
{
uint8_t v___x_2301_; 
v___x_2301_ = 0;
return v___x_2301_;
}
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ofNat___boxed(lean_object* v_n_2302_){
_start:
{
uint8_t v_res_2303_; lean_object* v_r_2304_; 
v_res_2303_ = l_IO_TaskState_ofNat(v_n_2302_);
lean_dec(v_n_2302_);
v_r_2304_ = lean_box(v_res_2303_);
return v_r_2304_;
}
}
LEAN_EXPORT uint8_t l_IO_instDecidableEqTaskState(uint8_t v_x_2305_, uint8_t v_y_2306_){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2307_ = lean_box(v_x_2305_);
v___x_2308_ = lean_obj_tag_nat(v___x_2307_);
lean_dec(v___x_2307_);
v___x_2309_ = lean_box(v_y_2306_);
v___x_2310_ = lean_obj_tag_nat(v___x_2309_);
lean_dec(v___x_2309_);
v___x_2311_ = lean_nat_dec_eq(v___x_2308_, v___x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_IO_instDecidableEqTaskState___boxed(lean_object* v_x_2312_, lean_object* v_y_2313_){
_start:
{
uint8_t v_x_23__boxed_2314_; uint8_t v_y_24__boxed_2315_; uint8_t v_res_2316_; lean_object* v_r_2317_; 
v_x_23__boxed_2314_ = lean_unbox(v_x_2312_);
v_y_24__boxed_2315_ = lean_unbox(v_y_2313_);
v_res_2316_ = l_IO_instDecidableEqTaskState(v_x_23__boxed_2314_, v_y_24__boxed_2315_);
v_r_2317_ = lean_box(v_res_2316_);
return v_r_2317_;
}
}
LEAN_EXPORT uint8_t l_IO_instOrdTaskState_ord(uint8_t v_x_2318_, uint8_t v_y_2319_){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v___x_2320_ = lean_box(v_x_2318_);
v___x_2321_ = lean_obj_tag_nat(v___x_2320_);
lean_dec(v___x_2320_);
v___x_2322_ = lean_box(v_y_2319_);
v___x_2323_ = lean_obj_tag_nat(v___x_2322_);
lean_dec(v___x_2322_);
v___x_2324_ = lean_nat_dec_lt(v___x_2321_, v___x_2323_);
if (v___x_2324_ == 0)
{
uint8_t v___x_2325_; 
v___x_2325_ = lean_nat_dec_eq(v___x_2321_, v___x_2323_);
if (v___x_2325_ == 0)
{
uint8_t v___x_2326_; 
v___x_2326_ = 2;
return v___x_2326_;
}
else
{
uint8_t v___x_2327_; 
v___x_2327_ = 1;
return v___x_2327_;
}
}
else
{
uint8_t v___x_2328_; 
v___x_2328_ = 0;
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instOrdTaskState_ord___boxed(lean_object* v_x_2329_, lean_object* v_y_2330_){
_start:
{
uint8_t v_x_33__boxed_2331_; uint8_t v_y_34__boxed_2332_; uint8_t v_res_2333_; lean_object* v_r_2334_; 
v_x_33__boxed_2331_ = lean_unbox(v_x_2329_);
v_y_34__boxed_2332_ = lean_unbox(v_y_2330_);
v_res_2333_ = l_IO_instOrdTaskState_ord(v_x_33__boxed_2331_, v_y_34__boxed_2332_);
v_r_2334_ = lean_box(v_res_2333_);
return v_r_2334_;
}
}
static lean_object* _init_l_IO_instLTTaskState(void){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = lean_box(0);
return v___x_2337_;
}
}
static lean_object* _init_l_IO_instLETaskState(void){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_box(0);
return v___x_2338_;
}
}
LEAN_EXPORT uint8_t l_IO_instMinTaskState___lam__0(uint8_t v_x_2339_, uint8_t v_y_2340_){
_start:
{
uint8_t v___x_2341_; 
v___x_2341_ = l_IO_instOrdTaskState_ord(v_x_2339_, v_y_2340_);
if (v___x_2341_ == 2)
{
return v_y_2340_;
}
else
{
return v_x_2339_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instMinTaskState___lam__0___boxed(lean_object* v_x_2342_, lean_object* v_y_2343_){
_start:
{
uint8_t v_x_boxed_2344_; uint8_t v_y_boxed_2345_; uint8_t v_res_2346_; lean_object* v_r_2347_; 
v_x_boxed_2344_ = lean_unbox(v_x_2342_);
v_y_boxed_2345_ = lean_unbox(v_y_2343_);
v_res_2346_ = l_IO_instMinTaskState___lam__0(v_x_boxed_2344_, v_y_boxed_2345_);
v_r_2347_ = lean_box(v_res_2346_);
return v_r_2347_;
}
}
LEAN_EXPORT uint8_t l_IO_instMaxTaskState___lam__0(uint8_t v_x_2350_, uint8_t v_y_2351_){
_start:
{
uint8_t v___x_2352_; 
v___x_2352_ = l_IO_instOrdTaskState_ord(v_x_2350_, v_y_2351_);
if (v___x_2352_ == 2)
{
return v_x_2350_;
}
else
{
return v_y_2351_;
}
}
}
LEAN_EXPORT lean_object* l_IO_instMaxTaskState___lam__0___boxed(lean_object* v_x_2353_, lean_object* v_y_2354_){
_start:
{
uint8_t v_x_boxed_2355_; uint8_t v_y_boxed_2356_; uint8_t v_res_2357_; lean_object* v_r_2358_; 
v_x_boxed_2355_ = lean_unbox(v_x_2353_);
v_y_boxed_2356_ = lean_unbox(v_y_2354_);
v_res_2357_ = l_IO_instMaxTaskState___lam__0(v_x_boxed_2355_, v_y_boxed_2356_);
v_r_2358_ = lean_box(v_res_2357_);
return v_r_2358_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toString(uint8_t v_x_2364_){
_start:
{
switch(v_x_2364_)
{
case 0:
{
lean_object* v___x_2365_; 
v___x_2365_ = ((lean_object*)(l_IO_TaskState_toString___closed__0));
return v___x_2365_;
}
case 1:
{
lean_object* v___x_2366_; 
v___x_2366_ = ((lean_object*)(l_IO_TaskState_toString___closed__1));
return v___x_2366_;
}
default: 
{
lean_object* v___x_2367_; 
v___x_2367_ = ((lean_object*)(l_IO_TaskState_toString___closed__2));
return v___x_2367_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_toString___boxed(lean_object* v_x_2368_){
_start:
{
uint8_t v_x_31__boxed_2369_; lean_object* v_res_2370_; 
v_x_31__boxed_2369_ = lean_unbox(v_x_2368_);
v_res_2370_ = l_IO_TaskState_toString(v_x_31__boxed_2369_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_IO_getTaskState___boxed(lean_object* v_00_u03b1_2376_, lean_object* v_a_00___x40___internal___hyg_2377_, lean_object* v_a_00___x40___internal___hyg_2378_){
_start:
{
uint8_t v_res_2379_; lean_object* v_r_2380_; 
v_res_2379_ = lean_io_get_task_state(v_a_00___x40___internal___hyg_2377_);
lean_dec_ref(v_a_00___x40___internal___hyg_2377_);
v_r_2380_ = lean_box(v_res_2379_);
return v_r_2380_;
}
}
LEAN_EXPORT uint8_t l_IO_hasFinished___redArg(lean_object* v_task_2381_){
_start:
{
uint8_t v___x_2383_; 
v___x_2383_ = lean_io_get_task_state(v_task_2381_);
if (v___x_2383_ == 2)
{
uint8_t v___x_2384_; 
v___x_2384_ = 1;
return v___x_2384_;
}
else
{
uint8_t v___x_2385_; 
v___x_2385_ = 0;
return v___x_2385_;
}
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___redArg___boxed(lean_object* v_task_2386_, lean_object* v_a_2387_){
_start:
{
uint8_t v_res_2388_; lean_object* v_r_2389_; 
v_res_2388_ = l_IO_hasFinished___redArg(v_task_2386_);
lean_dec_ref(v_task_2386_);
v_r_2389_ = lean_box(v_res_2388_);
return v_r_2389_;
}
}
LEAN_EXPORT uint8_t l_IO_hasFinished(lean_object* v_00_u03b1_2390_, lean_object* v_task_2391_){
_start:
{
uint8_t v___x_2393_; 
v___x_2393_ = lean_io_get_task_state(v_task_2391_);
if (v___x_2393_ == 2)
{
uint8_t v___x_2394_; 
v___x_2394_ = 1;
return v___x_2394_;
}
else
{
uint8_t v___x_2395_; 
v___x_2395_ = 0;
return v___x_2395_;
}
}
}
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object* v_00_u03b1_2396_, lean_object* v_task_2397_, lean_object* v_a_2398_){
_start:
{
uint8_t v_res_2399_; lean_object* v_r_2400_; 
v_res_2399_ = l_IO_hasFinished(v_00_u03b1_2396_, v_task_2397_);
lean_dec_ref(v_task_2397_);
v_r_2400_ = lean_box(v_res_2399_);
return v_r_2400_;
}
}
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object* v_00_u03b1_2404_, lean_object* v_t_2405_, lean_object* v_a_00___x40___internal___hyg_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = lean_io_wait(v_t_2405_);
return v_res_2407_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__10));
v___x_2435_ = l_Lean_mkAtom(v___x_2434_);
return v___x_2435_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__12, &l_IO_waitAny___auto__1___closed__12_once, _init_l_IO_waitAny___auto__1___closed__12);
v___x_2437_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2438_ = lean_array_push(v___x_2437_, v___x_2436_);
return v___x_2438_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2461_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__22));
v___x_2462_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2463_ = lean_array_push(v___x_2462_, v___x_2461_);
return v___x_2463_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__27(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__26));
v___x_2472_ = l_Lean_mkAtom(v___x_2471_);
return v___x_2472_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__28(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__27, &l_IO_waitAny___auto__1___closed__27_once, _init_l_IO_waitAny___auto__1___closed__27);
v___x_2474_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2475_ = lean_array_push(v___x_2474_, v___x_2473_);
return v___x_2475_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__29(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2476_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__28, &l_IO_waitAny___auto__1___closed__28_once, _init_l_IO_waitAny___auto__1___closed__28);
v___x_2477_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__25));
v___x_2478_ = lean_box(2);
v___x_2479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
lean_ctor_set(v___x_2479_, 1, v___x_2477_);
lean_ctor_set(v___x_2479_, 2, v___x_2476_);
return v___x_2479_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__30(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__29, &l_IO_waitAny___auto__1___closed__29_once, _init_l_IO_waitAny___auto__1___closed__29);
v___x_2481_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2482_ = lean_array_push(v___x_2481_, v___x_2480_);
return v___x_2482_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__31(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2483_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__30, &l_IO_waitAny___auto__1___closed__30_once, _init_l_IO_waitAny___auto__1___closed__30);
v___x_2484_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_2485_ = lean_box(2);
v___x_2486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
lean_ctor_set(v___x_2486_, 1, v___x_2484_);
lean_ctor_set(v___x_2486_, 2, v___x_2483_);
return v___x_2486_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__32(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__31, &l_IO_waitAny___auto__1___closed__31_once, _init_l_IO_waitAny___auto__1___closed__31);
v___x_2488_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__23, &l_IO_waitAny___auto__1___closed__23_once, _init_l_IO_waitAny___auto__1___closed__23);
v___x_2489_ = lean_array_push(v___x_2488_, v___x_2487_);
return v___x_2489_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__33(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2490_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__32, &l_IO_waitAny___auto__1___closed__32_once, _init_l_IO_waitAny___auto__1___closed__32);
v___x_2491_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_2492_ = lean_box(2);
v___x_2493_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
lean_ctor_set(v___x_2493_, 1, v___x_2491_);
lean_ctor_set(v___x_2493_, 2, v___x_2490_);
return v___x_2493_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__34(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__33, &l_IO_waitAny___auto__1___closed__33_once, _init_l_IO_waitAny___auto__1___closed__33);
v___x_2495_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__13, &l_IO_waitAny___auto__1___closed__13_once, _init_l_IO_waitAny___auto__1___closed__13);
v___x_2496_ = lean_array_push(v___x_2495_, v___x_2494_);
return v___x_2496_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__35(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2497_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__34, &l_IO_waitAny___auto__1___closed__34_once, _init_l_IO_waitAny___auto__1___closed__34);
v___x_2498_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__11));
v___x_2499_ = lean_box(2);
v___x_2500_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
lean_ctor_set(v___x_2500_, 1, v___x_2498_);
lean_ctor_set(v___x_2500_, 2, v___x_2497_);
return v___x_2500_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__36(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2501_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__35, &l_IO_waitAny___auto__1___closed__35_once, _init_l_IO_waitAny___auto__1___closed__35);
v___x_2502_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2503_ = lean_array_push(v___x_2502_, v___x_2501_);
return v___x_2503_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__37(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2504_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__36, &l_IO_waitAny___auto__1___closed__36_once, _init_l_IO_waitAny___auto__1___closed__36);
v___x_2505_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_2506_ = lean_box(2);
v___x_2507_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
lean_ctor_set(v___x_2507_, 1, v___x_2505_);
lean_ctor_set(v___x_2507_, 2, v___x_2504_);
return v___x_2507_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__38(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__37, &l_IO_waitAny___auto__1___closed__37_once, _init_l_IO_waitAny___auto__1___closed__37);
v___x_2509_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2510_ = lean_array_push(v___x_2509_, v___x_2508_);
return v___x_2510_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__39(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2511_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__38, &l_IO_waitAny___auto__1___closed__38_once, _init_l_IO_waitAny___auto__1___closed__38);
v___x_2512_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__7));
v___x_2513_ = lean_box(2);
v___x_2514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
lean_ctor_set(v___x_2514_, 1, v___x_2512_);
lean_ctor_set(v___x_2514_, 2, v___x_2511_);
return v___x_2514_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__40(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__39, &l_IO_waitAny___auto__1___closed__39_once, _init_l_IO_waitAny___auto__1___closed__39);
v___x_2516_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2517_ = lean_array_push(v___x_2516_, v___x_2515_);
return v___x_2517_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__41(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2518_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__40, &l_IO_waitAny___auto__1___closed__40_once, _init_l_IO_waitAny___auto__1___closed__40);
v___x_2519_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__4));
v___x_2520_ = lean_box(2);
v___x_2521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v___x_2519_);
lean_ctor_set(v___x_2521_, 2, v___x_2518_);
return v___x_2521_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1(void){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__41, &l_IO_waitAny___auto__1___closed__41_once, _init_l_IO_waitAny___auto__1___closed__41);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object* v_00_u03b1_2527_, lean_object* v_tasks_2528_, lean_object* v_h_2529_, lean_object* v_a_00___x40___internal___hyg_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = lean_io_wait_any(v_tasks_2528_);
lean_dec(v_tasks_2528_);
return v_res_2531_;
}
}
static lean_object* _init_l_IO_waitAny_x27___auto__1(void){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__41, &l_IO_waitAny___auto__1___closed__41_once, _init_l_IO_waitAny___auto__1___closed__41);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0(lean_object* v___x_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set(v___x_2535_, 1, v_a_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
if (lean_obj_tag(v_a_2536_) == 0)
{
lean_object* v___x_2538_; 
v___x_2538_ = lean_array_to_list(v_a_2537_);
return v___x_2538_;
}
else
{
lean_object* v_head_2539_; lean_object* v_tail_2540_; lean_object* v___x_2541_; lean_object* v___f_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v_head_2539_ = lean_ctor_get(v_a_2536_, 0);
lean_inc(v_head_2539_);
v_tail_2540_ = lean_ctor_get(v_a_2536_, 1);
lean_inc(v_tail_2540_);
lean_dec_ref_known(v_a_2536_, 2);
v___x_2541_ = lean_array_get_size(v_a_2537_);
v___f_2542_ = lean_alloc_closure((void*)(l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2542_, 0, v___x_2541_);
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = 1;
v___x_2545_ = lean_task_map(v___f_2542_, v_head_2539_, v___x_2543_, v___x_2544_);
v___x_2546_ = lean_array_push(v_a_2537_, v___x_2545_);
v_a_2536_ = v_tail_2540_;
v_a_2537_ = v___x_2546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg(lean_object* v_tasks_2550_){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_fst_2555_; lean_object* v_snd_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2564_; 
v___x_2552_ = ((lean_object*)(l_IO_waitAny_x27___redArg___closed__0));
lean_inc(v_tasks_2550_);
v___x_2553_ = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(v_tasks_2550_, v___x_2552_);
v___x_2554_ = lean_io_wait_any(v___x_2553_);
lean_dec(v___x_2553_);
v_fst_2555_ = lean_ctor_get(v___x_2554_, 0);
v_snd_2556_ = lean_ctor_get(v___x_2554_, 1);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2558_ = v___x_2554_;
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_snd_2556_);
lean_inc(v_fst_2555_);
lean_dec(v___x_2554_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2562_; 
lean_inc(v_tasks_2550_);
v___x_2560_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_box(0), v_tasks_2550_, v_tasks_2550_, v_fst_2555_, v___x_2552_);
lean_dec(v_tasks_2550_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 1, v___x_2560_);
lean_ctor_set(v___x_2558_, 0, v_snd_2556_);
v___x_2562_ = v___x_2558_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_snd_2556_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg___boxed(lean_object* v_tasks_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_IO_waitAny_x27___redArg(v_tasks_2565_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27(lean_object* v_00_u03b1_2568_, lean_object* v_tasks_2569_, lean_object* v_h_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_IO_waitAny_x27___redArg(v_tasks_2569_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___boxed(lean_object* v_00_u03b1_2573_, lean_object* v_tasks_2574_, lean_object* v_h_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_IO_waitAny_x27(v_00_u03b1_2573_, v_tasks_2574_, v_h_2575_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0(lean_object* v_00_u03b1_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(v_a_2579_, v_a_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object* v_a_00___x40___internal___hyg_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = lean_io_get_num_heartbeats();
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_IO_setNumHeartbeats___boxed(lean_object* v_count_2587_, lean_object* v_a_00___x40___internal___hyg_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = lean_io_set_heartbeats(v_count_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_IO_addHeartbeats(lean_object* v_count_2590_){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = lean_io_get_num_heartbeats();
v___x_2593_ = lean_nat_add(v___x_2592_, v_count_2590_);
lean_dec(v___x_2592_);
v___x_2594_ = lean_io_set_heartbeats(v___x_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_IO_addHeartbeats___boxed(lean_object* v_count_2595_, lean_object* v_a_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_IO_addHeartbeats(v_count_2595_);
lean_dec(v_count_2595_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx___impl(uint8_t v_x_2598_){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = lean_box(v_x_2598_);
v___x_2600_ = lean_obj_tag_nat(v___x_2599_);
lean_dec(v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx___impl___boxed(lean_object* v_x_2601_){
_start:
{
uint8_t v_x_4__boxed_2602_; lean_object* v_res_2603_; 
v_x_4__boxed_2602_ = lean_unbox(v_x_2601_);
v_res_2603_ = l_IO_FS_Mode_ctorIdx___impl(v_x_4__boxed_2602_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg(lean_object* v_k_2604_){
_start:
{
lean_inc(v_k_2604_);
return v_k_2604_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg___boxed(lean_object* v_k_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_IO_FS_Mode_ctorElim___redArg(v_k_2605_);
lean_dec(v_k_2605_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim(lean_object* v_motive_2607_, lean_object* v_ctorIdx_2608_, uint8_t v_t_2609_, lean_object* v_h_2610_, lean_object* v_k_2611_){
_start:
{
lean_inc(v_k_2611_);
return v_k_2611_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___boxed(lean_object* v_motive_2612_, lean_object* v_ctorIdx_2613_, lean_object* v_t_2614_, lean_object* v_h_2615_, lean_object* v_k_2616_){
_start:
{
uint8_t v_t_boxed_2617_; lean_object* v_res_2618_; 
v_t_boxed_2617_ = lean_unbox(v_t_2614_);
v_res_2618_ = l_IO_FS_Mode_ctorElim(v_motive_2612_, v_ctorIdx_2613_, v_t_boxed_2617_, v_h_2615_, v_k_2616_);
lean_dec(v_k_2616_);
lean_dec(v_ctorIdx_2613_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg(lean_object* v_read_2619_){
_start:
{
lean_inc(v_read_2619_);
return v_read_2619_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg___boxed(lean_object* v_read_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_IO_FS_Mode_read_elim___redArg(v_read_2620_);
lean_dec(v_read_2620_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim(lean_object* v_motive_2622_, uint8_t v_t_2623_, lean_object* v_h_2624_, lean_object* v_read_2625_){
_start:
{
lean_inc(v_read_2625_);
return v_read_2625_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___boxed(lean_object* v_motive_2626_, lean_object* v_t_2627_, lean_object* v_h_2628_, lean_object* v_read_2629_){
_start:
{
uint8_t v_t_boxed_2630_; lean_object* v_res_2631_; 
v_t_boxed_2630_ = lean_unbox(v_t_2627_);
v_res_2631_ = l_IO_FS_Mode_read_elim(v_motive_2626_, v_t_boxed_2630_, v_h_2628_, v_read_2629_);
lean_dec(v_read_2629_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg(lean_object* v_write_2632_){
_start:
{
lean_inc(v_write_2632_);
return v_write_2632_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg___boxed(lean_object* v_write_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_IO_FS_Mode_write_elim___redArg(v_write_2633_);
lean_dec(v_write_2633_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim(lean_object* v_motive_2635_, uint8_t v_t_2636_, lean_object* v_h_2637_, lean_object* v_write_2638_){
_start:
{
lean_inc(v_write_2638_);
return v_write_2638_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___boxed(lean_object* v_motive_2639_, lean_object* v_t_2640_, lean_object* v_h_2641_, lean_object* v_write_2642_){
_start:
{
uint8_t v_t_boxed_2643_; lean_object* v_res_2644_; 
v_t_boxed_2643_ = lean_unbox(v_t_2640_);
v_res_2644_ = l_IO_FS_Mode_write_elim(v_motive_2639_, v_t_boxed_2643_, v_h_2641_, v_write_2642_);
lean_dec(v_write_2642_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg(lean_object* v_writeNew_2645_){
_start:
{
lean_inc(v_writeNew_2645_);
return v_writeNew_2645_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg___boxed(lean_object* v_writeNew_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_IO_FS_Mode_writeNew_elim___redArg(v_writeNew_2646_);
lean_dec(v_writeNew_2646_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim(lean_object* v_motive_2648_, uint8_t v_t_2649_, lean_object* v_h_2650_, lean_object* v_writeNew_2651_){
_start:
{
lean_inc(v_writeNew_2651_);
return v_writeNew_2651_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___boxed(lean_object* v_motive_2652_, lean_object* v_t_2653_, lean_object* v_h_2654_, lean_object* v_writeNew_2655_){
_start:
{
uint8_t v_t_boxed_2656_; lean_object* v_res_2657_; 
v_t_boxed_2656_ = lean_unbox(v_t_2653_);
v_res_2657_ = l_IO_FS_Mode_writeNew_elim(v_motive_2652_, v_t_boxed_2656_, v_h_2654_, v_writeNew_2655_);
lean_dec(v_writeNew_2655_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg(lean_object* v_readWrite_2658_){
_start:
{
lean_inc(v_readWrite_2658_);
return v_readWrite_2658_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg___boxed(lean_object* v_readWrite_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_IO_FS_Mode_readWrite_elim___redArg(v_readWrite_2659_);
lean_dec(v_readWrite_2659_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim(lean_object* v_motive_2661_, uint8_t v_t_2662_, lean_object* v_h_2663_, lean_object* v_readWrite_2664_){
_start:
{
lean_inc(v_readWrite_2664_);
return v_readWrite_2664_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___boxed(lean_object* v_motive_2665_, lean_object* v_t_2666_, lean_object* v_h_2667_, lean_object* v_readWrite_2668_){
_start:
{
uint8_t v_t_boxed_2669_; lean_object* v_res_2670_; 
v_t_boxed_2669_ = lean_unbox(v_t_2666_);
v_res_2670_ = l_IO_FS_Mode_readWrite_elim(v_motive_2665_, v_t_boxed_2669_, v_h_2667_, v_readWrite_2668_);
lean_dec(v_readWrite_2668_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg(lean_object* v_append_2671_){
_start:
{
lean_inc(v_append_2671_);
return v_append_2671_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg___boxed(lean_object* v_append_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_IO_FS_Mode_append_elim___redArg(v_append_2672_);
lean_dec(v_append_2672_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim(lean_object* v_motive_2674_, uint8_t v_t_2675_, lean_object* v_h_2676_, lean_object* v_append_2677_){
_start:
{
lean_inc(v_append_2677_);
return v_append_2677_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___boxed(lean_object* v_motive_2678_, lean_object* v_t_2679_, lean_object* v_h_2680_, lean_object* v_append_2681_){
_start:
{
uint8_t v_t_boxed_2682_; lean_object* v_res_2683_; 
v_t_boxed_2682_ = lean_unbox(v_t_2679_);
v_res_2683_ = l_IO_FS_Mode_append_elim(v_motive_2678_, v_t_boxed_2682_, v_h_2680_, v_append_2681_);
lean_dec(v_append_2681_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0(){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0___boxed(lean_object* v___y_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_IO_FS_instInhabitedStream_default___lam__0();
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1(){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2693_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1___boxed(lean_object* v___y_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_IO_FS_instInhabitedStream_default___lam__1();
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2(lean_object* v_x_2697_){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2___boxed(lean_object* v_x_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_IO_FS_instInhabitedStream_default___lam__2(v_x_2701_);
lean_dec_ref(v_x_2701_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3(lean_object* v_x_2704_){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3___boxed(lean_object* v_x_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_IO_FS_instInhabitedStream_default___lam__3(v_x_2708_);
lean_dec_ref(v_x_2708_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4(size_t v_x_2711_){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4___boxed(lean_object* v_x_2715_, lean_object* v___y_2716_){
_start:
{
size_t v_x_193__boxed_2717_; lean_object* v_res_2718_; 
v_x_193__boxed_2717_ = lean_unbox_usize(v_x_2715_);
lean_dec(v_x_2715_);
v_res_2718_ = l_IO_FS_instInhabitedStream_default___lam__4(v_x_193__boxed_2717_);
return v_res_2718_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instInhabitedStream_default___lam__5(uint8_t v___x_2719_){
_start:
{
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__5___boxed(lean_object* v___x_2721_, lean_object* v___y_2722_){
_start:
{
uint8_t v___x_204__boxed_2723_; uint8_t v_res_2724_; lean_object* v_r_2725_; 
v___x_204__boxed_2723_ = lean_unbox(v___x_2721_);
v_res_2724_ = l_IO_FS_instInhabitedStream_default___lam__5(v___x_204__boxed_2723_);
v_r_2725_ = lean_box(v_res_2724_);
return v_r_2725_;
}
}
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object* v_a_00___x40___internal___hyg_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = lean_get_stdin();
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object* v_a_00___x40___internal___hyg_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = lean_get_stdout();
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object* v_a_00___x40___internal___hyg_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = lean_get_stderr();
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object* v_a_00___x40___internal___hyg_2754_, lean_object* v_a_00___x40___internal___hyg_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = lean_get_set_stdin(v_a_00___x40___internal___hyg_2754_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object* v_a_00___x40___internal___hyg_2759_, lean_object* v_a_00___x40___internal___hyg_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = lean_get_set_stdout(v_a_00___x40___internal___hyg_2759_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object* v_a_00___x40___internal___hyg_2764_, lean_object* v_a_00___x40___internal___hyg_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = lean_get_set_stderr(v_a_00___x40___internal___hyg_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_IO_iterate___redArg(lean_object* v_a_2767_, lean_object* v_f_2768_){
_start:
{
lean_object* v___x_2770_; 
lean_inc_ref(v_f_2768_);
v___x_2770_ = lean_apply_2(v_f_2768_, v_a_2767_, lean_box(0));
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2781_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2781_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2781_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
if (lean_obj_tag(v_a_2771_) == 0)
{
lean_object* v_val_2775_; 
lean_del_object(v___x_2773_);
v_val_2775_ = lean_ctor_get(v_a_2771_, 0);
lean_inc(v_val_2775_);
lean_dec_ref_known(v_a_2771_, 1);
v_a_2767_ = v_val_2775_;
goto _start;
}
else
{
lean_object* v_val_2777_; lean_object* v___x_2779_; 
lean_dec_ref(v_f_2768_);
v_val_2777_ = lean_ctor_get(v_a_2771_, 0);
lean_inc(v_val_2777_);
lean_dec_ref_known(v_a_2771_, 1);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 0, v_val_2777_);
v___x_2779_ = v___x_2773_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_val_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec_ref(v_f_2768_);
v_a_2782_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2770_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2770_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_iterate___redArg___boxed(lean_object* v_a_2790_, lean_object* v_f_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_IO_iterate___redArg(v_a_2790_, v_f_2791_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_IO_iterate(lean_object* v_00_u03b1_2794_, lean_object* v_00_u03b2_2795_, lean_object* v_a_2796_, lean_object* v_f_2797_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_IO_iterate___redArg(v_a_2796_, v_f_2797_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_IO_iterate___boxed(lean_object* v_00_u03b1_2800_, lean_object* v_00_u03b2_2801_, lean_object* v_a_2802_, lean_object* v_f_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_IO_iterate(v_00_u03b1_2800_, v_00_u03b2_2801_, v_a_2802_, v_f_2803_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object* v_fn_2809_, lean_object* v_mode_2810_, lean_object* v_a_00___x40___internal___hyg_2811_){
_start:
{
uint8_t v_mode_boxed_2812_; lean_object* v_res_2813_; 
v_mode_boxed_2812_ = lean_unbox(v_mode_2810_);
v_res_2813_ = lean_io_prim_handle_mk(v_fn_2809_, v_mode_boxed_2812_);
lean_dec_ref(v_fn_2809_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lock___boxed(lean_object* v_h_2817_, lean_object* v_exclusive_2818_, lean_object* v_a_00___x40___internal___hyg_2819_){
_start:
{
uint8_t v_exclusive_boxed_2820_; lean_object* v_res_2821_; 
v_exclusive_boxed_2820_ = lean_unbox(v_exclusive_2818_);
v_res_2821_ = lean_io_prim_handle_lock(v_h_2817_, v_exclusive_boxed_2820_);
lean_dec(v_h_2817_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_tryLock___boxed(lean_object* v_h_2825_, lean_object* v_exclusive_2826_, lean_object* v_a_00___x40___internal___hyg_2827_){
_start:
{
uint8_t v_exclusive_boxed_2828_; lean_object* v_res_2829_; 
v_exclusive_boxed_2828_ = lean_unbox(v_exclusive_2826_);
v_res_2829_ = lean_io_prim_handle_try_lock(v_h_2825_, v_exclusive_boxed_2828_);
lean_dec(v_h_2825_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_unlock___boxed(lean_object* v_h_2832_, lean_object* v_a_00___x40___internal___hyg_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = lean_io_prim_handle_unlock(v_h_2832_);
lean_dec(v_h_2832_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_isTty___boxed(lean_object* v_h_2837_, lean_object* v_a_00___x40___internal___hyg_2838_){
_start:
{
uint8_t v_res_2839_; lean_object* v_r_2840_; 
v_res_2839_ = lean_io_prim_handle_is_tty(v_h_2837_);
lean_dec(v_h_2837_);
v_r_2840_ = lean_box(v_res_2839_);
return v_r_2840_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object* v_h_2843_, lean_object* v_a_00___x40___internal___hyg_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = lean_io_prim_handle_flush(v_h_2843_);
lean_dec(v_h_2843_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_rewind___boxed(lean_object* v_h_2848_, lean_object* v_a_00___x40___internal___hyg_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = lean_io_prim_handle_rewind(v_h_2848_);
lean_dec(v_h_2848_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_truncate___boxed(lean_object* v_h_2853_, lean_object* v_a_00___x40___internal___hyg_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = lean_io_prim_handle_truncate(v_h_2853_);
lean_dec(v_h_2853_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_read___boxed(lean_object* v_h_2859_, lean_object* v_bytes_2860_, lean_object* v_a_00___x40___internal___hyg_2861_){
_start:
{
size_t v_bytes_boxed_2862_; lean_object* v_res_2863_; 
v_bytes_boxed_2862_ = lean_unbox_usize(v_bytes_2860_);
lean_dec(v_bytes_2860_);
v_res_2863_ = lean_io_prim_handle_read(v_h_2859_, v_bytes_boxed_2862_);
lean_dec(v_h_2859_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object* v_h_2867_, lean_object* v_buffer_2868_, lean_object* v_a_00___x40___internal___hyg_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = lean_io_prim_handle_write(v_h_2867_, v_buffer_2868_);
lean_dec_ref(v_buffer_2868_);
lean_dec(v_h_2867_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object* v_h_2873_, lean_object* v_a_00___x40___internal___hyg_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = lean_io_prim_handle_get_line(v_h_2873_);
lean_dec(v_h_2873_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object* v_h_2879_, lean_object* v_s_2880_, lean_object* v_a_00___x40___internal___hyg_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = lean_io_prim_handle_put_str(v_h_2879_, v_s_2880_);
lean_dec_ref(v_s_2880_);
lean_dec(v_h_2879_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object* v_fname_2885_, lean_object* v_a_00___x40___internal___hyg_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = lean_io_realpath(v_fname_2885_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object* v_fname_2890_, lean_object* v_a_00___x40___internal___hyg_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = lean_io_remove_file(v_fname_2890_);
lean_dec_ref(v_fname_2890_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object* v_a_00___x40___internal___hyg_2895_, lean_object* v_a_00___x40___internal___hyg_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = lean_io_remove_dir(v_a_00___x40___internal___hyg_2895_);
lean_dec_ref(v_a_00___x40___internal___hyg_2895_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object* v_a_00___x40___internal___hyg_2900_, lean_object* v_a_00___x40___internal___hyg_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = lean_io_create_dir(v_a_00___x40___internal___hyg_2900_);
lean_dec_ref(v_a_00___x40___internal___hyg_2900_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_rename___boxed(lean_object* v_old_2906_, lean_object* v_new_2907_, lean_object* v_a_00___x40___internal___hyg_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = lean_io_rename(v_old_2906_, v_new_2907_);
lean_dec_ref(v_new_2907_);
lean_dec_ref(v_old_2906_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_renameIfNew___boxed(lean_object* v_old_2913_, lean_object* v_new_2914_, lean_object* v_a_00___x40___internal___hyg_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = lean_io_rename_if_new(v_old_2913_, v_new_2914_);
lean_dec_ref(v_new_2914_);
lean_dec_ref(v_old_2913_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_hardLink___boxed(lean_object* v_orig_2920_, lean_object* v_link_2921_, lean_object* v_a_00___x40___internal___hyg_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = lean_io_hard_link(v_orig_2920_, v_link_2921_);
lean_dec_ref(v_link_2921_);
lean_dec_ref(v_orig_2920_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createTempFile___boxed(lean_object* v_a_00___x40___internal___hyg_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = lean_io_create_tempfile();
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createTempDir___boxed(lean_object* v_a_00___x40___internal___hyg_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = lean_io_create_tempdir();
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object* v_var_2932_, lean_object* v_a_00___x40___internal___hyg_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = lean_io_getenv(v_var_2932_);
lean_dec_ref(v_var_2932_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object* v_a_00___x40___internal___hyg_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = lean_io_app_path();
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object* v_a_00___x40___internal___hyg_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = lean_io_current_dir();
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg(lean_object* v_fn_2941_, uint8_t v_mode_2942_, lean_object* v_f_2943_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = lean_io_prim_handle_mk(v_fn_2941_, v_mode_2942_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
v___x_2947_ = lean_apply_2(v_f_2943_, v_a_2946_, lean_box(0));
return v___x_2947_;
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec_ref(v_f_2943_);
v_a_2948_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2945_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2945_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg___boxed(lean_object* v_fn_2956_, lean_object* v_mode_2957_, lean_object* v_f_2958_, lean_object* v_a_2959_){
_start:
{
uint8_t v_mode_boxed_2960_; lean_object* v_res_2961_; 
v_mode_boxed_2960_ = lean_unbox(v_mode_2957_);
v_res_2961_ = l_IO_FS_withFile___redArg(v_fn_2956_, v_mode_boxed_2960_, v_f_2958_);
lean_dec_ref(v_fn_2956_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile(lean_object* v_00_u03b1_2962_, lean_object* v_fn_2963_, uint8_t v_mode_2964_, lean_object* v_f_2965_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_io_prim_handle_mk(v_fn_2963_, v_mode_2964_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2969_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
v___x_2969_ = lean_apply_2(v_f_2965_, v_a_2968_, lean_box(0));
return v___x_2969_;
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec_ref(v_f_2965_);
v_a_2970_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2967_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2967_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___boxed(lean_object* v_00_u03b1_2978_, lean_object* v_fn_2979_, lean_object* v_mode_2980_, lean_object* v_f_2981_, lean_object* v_a_2982_){
_start:
{
uint8_t v_mode_boxed_2983_; lean_object* v_res_2984_; 
v_mode_boxed_2983_ = lean_unbox(v_mode_2980_);
v_res_2984_ = l_IO_FS_withFile(v_00_u03b1_2978_, v_fn_2979_, v_mode_boxed_2983_, v_f_2981_);
lean_dec_ref(v_fn_2979_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn(lean_object* v_h_2985_, lean_object* v_s_2986_){
_start:
{
uint32_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = 10;
v___x_2989_ = lean_string_push(v_s_2986_, v___x_2988_);
v___x_2990_ = lean_io_prim_handle_put_str(v_h_2985_, v___x_2989_);
lean_dec_ref(v___x_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object* v_h_2991_, lean_object* v_s_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_IO_FS_Handle_putStrLn(v_h_2991_, v_s_2992_);
lean_dec(v_h_2991_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(lean_object* v_h_2995_, lean_object* v_acc_2996_){
_start:
{
size_t v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = ((size_t)1024ULL);
v___x_2999_ = lean_io_prim_handle_read(v_h_2995_, v___x_2998_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3013_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3002_ = v___x_2999_;
v_isShared_3003_ = v_isSharedCheck_3013_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2999_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3013_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
uint8_t v___x_3004_; 
v___x_3004_ = l_ByteArray_isEmpty(v_a_3000_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
lean_del_object(v___x_3002_);
v___x_3005_ = lean_unsigned_to_nat(0u);
v___x_3006_ = lean_byte_array_size(v_acc_2996_);
v___x_3007_ = lean_byte_array_size(v_a_3000_);
v___x_3008_ = lean_byte_array_copy_slice(v_a_3000_, v___x_3005_, v_acc_2996_, v___x_3006_, v___x_3007_, v___x_3004_);
lean_dec(v_a_3000_);
v_acc_2996_ = v___x_3008_;
goto _start;
}
else
{
lean_object* v___x_3011_; 
lean_dec(v_a_3000_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v_acc_2996_);
v___x_3011_ = v___x_3002_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_acc_2996_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
else
{
lean_dec_ref(v_acc_2996_);
return v___x_2999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop___boxed(lean_object* v_h_3014_, lean_object* v_acc_3015_, lean_object* v_a_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_3014_, v_acc_3015_);
lean_dec(v_h_3014_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto(lean_object* v_h_3018_, lean_object* v_buf_3019_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_3018_, v_buf_3019_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto___boxed(lean_object* v_h_3022_, lean_object* v_buf_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_IO_FS_Handle_readBinToEndInto(v_h_3022_, v_buf_3023_);
lean_dec(v_h_3022_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd(lean_object* v_h_3026_){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = l_ByteArray_empty;
v___x_3029_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_3026_, v___x_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object* v_h_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_IO_FS_Handle_readBinToEnd(v_h_3030_);
lean_dec(v_h_3030_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd(lean_object* v_h_3036_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l_IO_FS_Handle_readBinToEnd(v_h_3036_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3052_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3052_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3052_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
uint8_t v___x_3043_; 
v___x_3043_ = lean_string_validate_utf8(v_a_3039_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; lean_object* v___x_3046_; 
lean_dec(v_a_3039_);
v___x_3044_ = ((lean_object*)(l_IO_FS_Handle_readToEnd___closed__1));
if (v_isShared_3042_ == 0)
{
lean_ctor_set_tag(v___x_3041_, 1);
lean_ctor_set(v___x_3041_, 0, v___x_3044_);
v___x_3046_ = v___x_3041_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
else
{
lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3048_ = lean_string_from_utf8_unchecked(v_a_3039_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3048_);
v___x_3050_ = v___x_3041_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
v_a_3053_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3038_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3038_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object* v_h_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_IO_FS_Handle_readToEnd(v_h_3061_);
lean_dec(v_h_3061_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read(lean_object* v_h_3064_, lean_object* v_lines_3065_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = lean_io_prim_handle_get_line(v_h_3064_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3125_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3070_ = v___x_3067_;
v_isShared_3071_ = v_isSharedCheck_3125_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3067_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3125_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___y_3073_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; uint32_t v___y_3080_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; uint32_t v___y_3093_; lean_object* v___x_3115_; lean_object* v___x_3116_; uint8_t v___x_3117_; 
v___x_3115_ = lean_string_utf8_byte_size(v_a_3068_);
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = lean_nat_dec_eq(v___x_3115_, v___x_3116_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
lean_inc(v_a_3068_);
v___x_3118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3118_, 0, v_a_3068_);
lean_ctor_set(v___x_3118_, 1, v___x_3116_);
lean_ctor_set(v___x_3118_, 2, v___x_3115_);
v___x_3119_ = l_String_Slice_Pos_prev_x3f(v___x_3118_, v___x_3115_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_dec_ref_known(v___x_3118_, 3);
goto v___jp_3113_;
}
else
{
lean_object* v_val_3120_; lean_object* v___x_3121_; 
v_val_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_val_3120_);
lean_dec_ref_known(v___x_3119_, 1);
v___x_3121_ = l_String_Slice_Pos_get_x3f(v___x_3118_, v_val_3120_);
lean_dec(v_val_3120_);
lean_dec_ref_known(v___x_3118_, 3);
if (lean_obj_tag(v___x_3121_) == 0)
{
goto v___jp_3113_;
}
else
{
lean_object* v_val_3122_; uint32_t v___x_3123_; 
v_val_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_val_3122_);
lean_dec_ref_known(v___x_3121_, 1);
v___x_3123_ = lean_unbox_uint32(v_val_3122_);
lean_dec(v_val_3122_);
v___y_3093_ = v___x_3123_;
goto v___jp_3092_;
}
}
}
else
{
lean_object* v___x_3124_; 
lean_del_object(v___x_3070_);
lean_dec(v_a_3068_);
v___x_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3124_, 0, v_lines_3065_);
return v___x_3124_;
}
v___jp_3072_:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_array_push(v_lines_3065_, v___y_3073_);
v_lines_3065_ = v___x_3074_;
goto _start;
}
v___jp_3076_:
{
uint32_t v___x_3081_; uint8_t v___x_3082_; 
v___x_3081_ = 13;
v___x_3082_ = lean_uint32_dec_eq(v___y_3080_, v___x_3081_);
if (v___x_3082_ == 0)
{
lean_dec(v___y_3079_);
lean_dec(v___y_3078_);
v___y_3073_ = v___y_3077_;
goto v___jp_3072_;
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3083_ = lean_string_utf8_byte_size(v___y_3077_);
lean_inc(v___y_3079_);
lean_inc_ref(v___y_3077_);
v___x_3084_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3084_, 0, v___y_3077_);
lean_ctor_set(v___x_3084_, 1, v___y_3079_);
lean_ctor_set(v___x_3084_, 2, v___x_3083_);
v___x_3085_ = l_String_Slice_Pos_prevn(v___x_3084_, v___x_3083_, v___y_3078_);
lean_dec_ref_known(v___x_3084_, 3);
v___x_3086_ = lean_string_utf8_extract_fast(v___y_3077_, v___y_3079_, v___x_3085_);
lean_dec(v___x_3085_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3077_);
v___y_3073_ = v___x_3086_;
goto v___jp_3072_;
}
}
v___jp_3087_:
{
uint32_t v___x_3091_; 
v___x_3091_ = 65;
v___y_3077_ = v___y_3088_;
v___y_3078_ = v___y_3089_;
v___y_3079_ = v___y_3090_;
v___y_3080_ = v___x_3091_;
goto v___jp_3076_;
}
v___jp_3092_:
{
uint32_t v___x_3094_; uint8_t v___x_3095_; 
v___x_3094_ = 10;
v___x_3095_ = lean_uint32_dec_eq(v___y_3093_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3096_ = lean_array_push(v_lines_3065_, v_a_3068_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v___x_3096_);
v___x_3098_ = v___x_3070_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3096_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
lean_del_object(v___x_3070_);
v___x_3100_ = lean_unsigned_to_nat(1u);
v___x_3101_ = lean_unsigned_to_nat(0u);
v___x_3102_ = lean_string_utf8_byte_size(v_a_3068_);
lean_inc(v_a_3068_);
v___x_3103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3103_, 0, v_a_3068_);
lean_ctor_set(v___x_3103_, 1, v___x_3101_);
lean_ctor_set(v___x_3103_, 2, v___x_3102_);
v___x_3104_ = l_String_Slice_Pos_prevn(v___x_3103_, v___x_3102_, v___x_3100_);
lean_dec_ref_known(v___x_3103_, 3);
v___x_3105_ = lean_string_utf8_extract_fast(v_a_3068_, v___x_3101_, v___x_3104_);
lean_dec(v___x_3104_);
lean_dec(v_a_3068_);
v___x_3106_ = lean_string_utf8_byte_size(v___x_3105_);
lean_inc_ref(v___x_3105_);
v___x_3107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3105_);
lean_ctor_set(v___x_3107_, 1, v___x_3101_);
lean_ctor_set(v___x_3107_, 2, v___x_3106_);
v___x_3108_ = l_String_Slice_Pos_prev_x3f(v___x_3107_, v___x_3106_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_dec_ref_known(v___x_3107_, 3);
v___y_3088_ = v___x_3105_;
v___y_3089_ = v___x_3100_;
v___y_3090_ = v___x_3101_;
goto v___jp_3087_;
}
else
{
lean_object* v_val_3109_; lean_object* v___x_3110_; 
v_val_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_val_3109_);
lean_dec_ref_known(v___x_3108_, 1);
v___x_3110_ = l_String_Slice_Pos_get_x3f(v___x_3107_, v_val_3109_);
lean_dec(v_val_3109_);
lean_dec_ref_known(v___x_3107_, 3);
if (lean_obj_tag(v___x_3110_) == 0)
{
v___y_3088_ = v___x_3105_;
v___y_3089_ = v___x_3100_;
v___y_3090_ = v___x_3101_;
goto v___jp_3087_;
}
else
{
lean_object* v_val_3111_; uint32_t v___x_3112_; 
v_val_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_val_3111_);
lean_dec_ref_known(v___x_3110_, 1);
v___x_3112_ = lean_unbox_uint32(v_val_3111_);
lean_dec(v_val_3111_);
v___y_3077_ = v___x_3105_;
v___y_3078_ = v___x_3100_;
v___y_3079_ = v___x_3101_;
v___y_3080_ = v___x_3112_;
goto v___jp_3076_;
}
}
}
}
v___jp_3113_:
{
uint32_t v___x_3114_; 
v___x_3114_ = 65;
v___y_3093_ = v___x_3114_;
goto v___jp_3092_;
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v_lines_3065_);
v_a_3126_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3067_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3067_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read___boxed(lean_object* v_h_3134_, lean_object* v_lines_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_3134_, v_lines_3135_);
lean_dec(v_h_3134_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines(lean_object* v_h_3140_){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_3143_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_3140_, v___x_3142_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines___boxed(lean_object* v_h_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_IO_FS_Handle_lines(v_h_3144_);
lean_dec(v_h_3144_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object* v_fname_3147_){
_start:
{
uint8_t v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = 0;
v___x_3150_ = lean_io_prim_handle_mk(v_fname_3147_, v___x_3149_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3152_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
lean_dec_ref_known(v___x_3150_, 1);
v___x_3152_ = l_IO_FS_Handle_lines(v_a_3151_);
lean_dec(v_a_3151_);
return v___x_3152_;
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
v_a_3153_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3150_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3150_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
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
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object* v_fname_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_IO_FS_lines(v_fname_3161_);
lean_dec_ref(v_fname_3161_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object* v_fname_3164_, lean_object* v_content_3165_){
_start:
{
uint8_t v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = 1;
v___x_3168_ = lean_io_prim_handle_mk(v_fname_3164_, v___x_3167_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3170_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref_known(v___x_3168_, 1);
v___x_3170_ = lean_io_prim_handle_write(v_a_3169_, v_content_3165_);
lean_dec(v_a_3169_);
return v___x_3170_;
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
v_a_3171_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3168_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3168_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object* v_fname_3179_, lean_object* v_content_3180_, lean_object* v_a_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_IO_FS_writeBinFile(v_fname_3179_, v_content_3180_);
lean_dec_ref(v_content_3180_);
lean_dec_ref(v_fname_3179_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object* v_fname_3183_, lean_object* v_content_3184_){
_start:
{
uint8_t v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = 1;
v___x_3187_ = lean_io_prim_handle_mk(v_fname_3183_, v___x_3186_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3189_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v___x_3187_, 1);
v___x_3189_ = lean_io_prim_handle_put_str(v_a_3188_, v_content_3184_);
lean_dec(v_a_3188_);
return v___x_3189_;
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
v_a_3190_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3187_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3187_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object* v_fname_3198_, lean_object* v_content_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_IO_FS_writeFile(v_fname_3198_, v_content_3199_);
lean_dec_ref(v_content_3199_);
lean_dec_ref(v_fname_3198_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object* v_strm_3202_, lean_object* v_s_3203_){
_start:
{
lean_object* v_putStr_3205_; uint32_t v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v_putStr_3205_ = lean_ctor_get(v_strm_3202_, 4);
lean_inc_ref(v_putStr_3205_);
lean_dec_ref(v_strm_3202_);
v___x_3206_ = 10;
v___x_3207_ = lean_string_push(v_s_3203_, v___x_3206_);
v___x_3208_ = lean_apply_2(v_putStr_3205_, v___x_3207_, lean_box(0));
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn___boxed(lean_object* v_strm_3209_, lean_object* v_s_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_IO_FS_Stream_putStrLn(v_strm_3209_, v_s_3210_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00IO_FS_instReprDirEntry_repr_spec__0(lean_object* v_a_3213_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_nat_to_int(v_a_3213_);
return v___x_3214_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = lean_unsigned_to_nat(8u);
v___x_3229_ = lean_nat_to_int(v___x_3228_);
return v___x_3229_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = lean_unsigned_to_nat(12u);
v___x_3240_ = lean_nat_to_int(v___x_3239_);
return v___x_3240_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__0));
v___x_3243_ = lean_string_length(v___x_3242_);
return v___x_3243_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__16, &l_IO_FS_instReprDirEntry_repr___redArg___closed__16_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16);
v___x_3245_ = lean_nat_to_int(v___x_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___redArg(lean_object* v_x_3250_){
_start:
{
lean_object* v_root_3251_; lean_object* v_fileName_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3291_; 
v_root_3251_ = lean_ctor_get(v_x_3250_, 0);
v_fileName_3252_ = lean_ctor_get(v_x_3250_, 1);
v_isSharedCheck_3291_ = !lean_is_exclusive(v_x_3250_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3254_ = v_x_3250_;
v_isShared_3255_ = v_isSharedCheck_3291_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_fileName_3252_);
lean_inc(v_root_3251_);
lean_dec(v_x_3250_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3291_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3256_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3257_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__6));
v___x_3258_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3259_ = lean_unsigned_to_nat(0u);
v___x_3260_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__9));
v___x_3261_ = l_String_quote(v_root_3251_);
v___x_3262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set_tag(v___x_3254_, 5);
lean_ctor_set(v___x_3254_, 1, v___x_3262_);
lean_ctor_set(v___x_3254_, 0, v___x_3260_);
v___x_3264_ = v___x_3254_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3260_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; uint8_t v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3265_ = l_Repr_addAppParen(v___x_3264_, v___x_3259_);
v___x_3266_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3258_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
v___x_3267_ = 0;
v___x_3268_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3268_, 0, v___x_3266_);
lean_ctor_set_uint8(v___x_3268_, sizeof(void*)*1, v___x_3267_);
v___x_3269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3257_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3269_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = lean_box(1);
v___x_3273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3271_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__13));
v___x_3275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3273_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
v___x_3276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
lean_ctor_set(v___x_3276_, 1, v___x_3256_);
v___x_3277_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__14, &l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14);
v___x_3278_ = l_String_quote(v_fileName_3252_);
v___x_3279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
v___x_3280_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3277_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
lean_ctor_set_uint8(v___x_3281_, sizeof(void*)*1, v___x_3267_);
v___x_3282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3276_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3283_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3284_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
lean_ctor_set(v___x_3285_, 1, v___x_3282_);
v___x_3286_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3283_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
lean_ctor_set_uint8(v___x_3289_, sizeof(void*)*1, v___x_3267_);
return v___x_3289_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr(lean_object* v_x_3292_, lean_object* v_prec_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_IO_FS_instReprDirEntry_repr___redArg(v_x_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___boxed(lean_object* v_x_3295_, lean_object* v_prec_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_IO_FS_instReprDirEntry_repr(v_x_3295_, v_prec_3296_);
lean_dec(v_prec_3296_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object* v_entry_3300_){
_start:
{
lean_object* v_root_3301_; lean_object* v_fileName_3302_; lean_object* v___x_3303_; 
v_root_3301_ = lean_ctor_get(v_entry_3300_, 0);
lean_inc_ref(v_root_3301_);
v_fileName_3302_ = lean_ctor_get(v_entry_3300_, 1);
lean_inc_ref(v_fileName_3302_);
lean_dec_ref(v_entry_3300_);
v___x_3303_ = l_System_FilePath_join(v_root_3301_, v_fileName_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx___impl(uint8_t v_x_3304_){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = lean_box(v_x_3304_);
v___x_3306_ = lean_obj_tag_nat(v___x_3305_);
lean_dec(v___x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx___impl___boxed(lean_object* v_x_3307_){
_start:
{
uint8_t v_x_4__boxed_3308_; lean_object* v_res_3309_; 
v_x_4__boxed_3308_ = lean_unbox(v_x_3307_);
v_res_3309_ = l_IO_FS_FileType_ctorIdx___impl(v_x_4__boxed_3308_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg(lean_object* v_k_3310_){
_start:
{
lean_inc(v_k_3310_);
return v_k_3310_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg___boxed(lean_object* v_k_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_IO_FS_FileType_ctorElim___redArg(v_k_3311_);
lean_dec(v_k_3311_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim(lean_object* v_motive_3313_, lean_object* v_ctorIdx_3314_, uint8_t v_t_3315_, lean_object* v_h_3316_, lean_object* v_k_3317_){
_start:
{
lean_inc(v_k_3317_);
return v_k_3317_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___boxed(lean_object* v_motive_3318_, lean_object* v_ctorIdx_3319_, lean_object* v_t_3320_, lean_object* v_h_3321_, lean_object* v_k_3322_){
_start:
{
uint8_t v_t_boxed_3323_; lean_object* v_res_3324_; 
v_t_boxed_3323_ = lean_unbox(v_t_3320_);
v_res_3324_ = l_IO_FS_FileType_ctorElim(v_motive_3318_, v_ctorIdx_3319_, v_t_boxed_3323_, v_h_3321_, v_k_3322_);
lean_dec(v_k_3322_);
lean_dec(v_ctorIdx_3319_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg(lean_object* v_dir_3325_){
_start:
{
lean_inc(v_dir_3325_);
return v_dir_3325_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg___boxed(lean_object* v_dir_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_IO_FS_FileType_dir_elim___redArg(v_dir_3326_);
lean_dec(v_dir_3326_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim(lean_object* v_motive_3328_, uint8_t v_t_3329_, lean_object* v_h_3330_, lean_object* v_dir_3331_){
_start:
{
lean_inc(v_dir_3331_);
return v_dir_3331_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___boxed(lean_object* v_motive_3332_, lean_object* v_t_3333_, lean_object* v_h_3334_, lean_object* v_dir_3335_){
_start:
{
uint8_t v_t_boxed_3336_; lean_object* v_res_3337_; 
v_t_boxed_3336_ = lean_unbox(v_t_3333_);
v_res_3337_ = l_IO_FS_FileType_dir_elim(v_motive_3332_, v_t_boxed_3336_, v_h_3334_, v_dir_3335_);
lean_dec(v_dir_3335_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg(lean_object* v_file_3338_){
_start:
{
lean_inc(v_file_3338_);
return v_file_3338_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg___boxed(lean_object* v_file_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_IO_FS_FileType_file_elim___redArg(v_file_3339_);
lean_dec(v_file_3339_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim(lean_object* v_motive_3341_, uint8_t v_t_3342_, lean_object* v_h_3343_, lean_object* v_file_3344_){
_start:
{
lean_inc(v_file_3344_);
return v_file_3344_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___boxed(lean_object* v_motive_3345_, lean_object* v_t_3346_, lean_object* v_h_3347_, lean_object* v_file_3348_){
_start:
{
uint8_t v_t_boxed_3349_; lean_object* v_res_3350_; 
v_t_boxed_3349_ = lean_unbox(v_t_3346_);
v_res_3350_ = l_IO_FS_FileType_file_elim(v_motive_3345_, v_t_boxed_3349_, v_h_3347_, v_file_3348_);
lean_dec(v_file_3348_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg(lean_object* v_symlink_3351_){
_start:
{
lean_inc(v_symlink_3351_);
return v_symlink_3351_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg___boxed(lean_object* v_symlink_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_IO_FS_FileType_symlink_elim___redArg(v_symlink_3352_);
lean_dec(v_symlink_3352_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim(lean_object* v_motive_3354_, uint8_t v_t_3355_, lean_object* v_h_3356_, lean_object* v_symlink_3357_){
_start:
{
lean_inc(v_symlink_3357_);
return v_symlink_3357_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___boxed(lean_object* v_motive_3358_, lean_object* v_t_3359_, lean_object* v_h_3360_, lean_object* v_symlink_3361_){
_start:
{
uint8_t v_t_boxed_3362_; lean_object* v_res_3363_; 
v_t_boxed_3362_ = lean_unbox(v_t_3359_);
v_res_3363_ = l_IO_FS_FileType_symlink_elim(v_motive_3358_, v_t_boxed_3362_, v_h_3360_, v_symlink_3361_);
lean_dec(v_symlink_3361_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg(lean_object* v_other_3364_){
_start:
{
lean_inc(v_other_3364_);
return v_other_3364_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg___boxed(lean_object* v_other_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_IO_FS_FileType_other_elim___redArg(v_other_3365_);
lean_dec(v_other_3365_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim(lean_object* v_motive_3367_, uint8_t v_t_3368_, lean_object* v_h_3369_, lean_object* v_other_3370_){
_start:
{
lean_inc(v_other_3370_);
return v_other_3370_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___boxed(lean_object* v_motive_3371_, lean_object* v_t_3372_, lean_object* v_h_3373_, lean_object* v_other_3374_){
_start:
{
uint8_t v_t_boxed_3375_; lean_object* v_res_3376_; 
v_t_boxed_3375_ = lean_unbox(v_t_3372_);
v_res_3376_ = l_IO_FS_FileType_other_elim(v_motive_3371_, v_t_boxed_3375_, v_h_3373_, v_other_3374_);
lean_dec(v_other_3374_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr(uint8_t v_x_3389_, lean_object* v_prec_3390_){
_start:
{
lean_object* v___y_3392_; lean_object* v___y_3399_; lean_object* v___y_3406_; lean_object* v___y_3413_; 
switch(v_x_3389_)
{
case 0:
{
lean_object* v___x_3419_; uint8_t v___x_3420_; 
v___x_3419_ = lean_unsigned_to_nat(1024u);
v___x_3420_ = lean_nat_dec_le(v___x_3419_, v_prec_3390_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3392_ = v___x_3421_;
goto v___jp_3391_;
}
else
{
lean_object* v___x_3422_; 
v___x_3422_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3392_ = v___x_3422_;
goto v___jp_3391_;
}
}
case 1:
{
lean_object* v___x_3423_; uint8_t v___x_3424_; 
v___x_3423_ = lean_unsigned_to_nat(1024u);
v___x_3424_ = lean_nat_dec_le(v___x_3423_, v_prec_3390_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3399_ = v___x_3425_;
goto v___jp_3398_;
}
else
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3399_ = v___x_3426_;
goto v___jp_3398_;
}
}
case 2:
{
lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3427_ = lean_unsigned_to_nat(1024u);
v___x_3428_ = lean_nat_dec_le(v___x_3427_, v_prec_3390_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3406_ = v___x_3429_;
goto v___jp_3405_;
}
else
{
lean_object* v___x_3430_; 
v___x_3430_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3406_ = v___x_3430_;
goto v___jp_3405_;
}
}
default: 
{
lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3431_ = lean_unsigned_to_nat(1024u);
v___x_3432_ = lean_nat_dec_le(v___x_3431_, v_prec_3390_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; 
v___x_3433_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3413_ = v___x_3433_;
goto v___jp_3412_;
}
else
{
lean_object* v___x_3434_; 
v___x_3434_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3413_ = v___x_3434_;
goto v___jp_3412_;
}
}
}
v___jp_3391_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3393_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__1));
lean_inc(v___y_3392_);
v___x_3394_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___y_3392_);
lean_ctor_set(v___x_3394_, 1, v___x_3393_);
v___x_3395_ = 0;
v___x_3396_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3396_, 0, v___x_3394_);
lean_ctor_set_uint8(v___x_3396_, sizeof(void*)*1, v___x_3395_);
v___x_3397_ = l_Repr_addAppParen(v___x_3396_, v_prec_3390_);
return v___x_3397_;
}
v___jp_3398_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3400_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__3));
lean_inc(v___y_3399_);
v___x_3401_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___y_3399_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = 0;
v___x_3403_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3403_, 0, v___x_3401_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*1, v___x_3402_);
v___x_3404_ = l_Repr_addAppParen(v___x_3403_, v_prec_3390_);
return v___x_3404_;
}
v___jp_3405_:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3407_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__5));
lean_inc(v___y_3406_);
v___x_3408_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___y_3406_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
v___x_3409_ = 0;
v___x_3410_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3410_, 0, v___x_3408_);
lean_ctor_set_uint8(v___x_3410_, sizeof(void*)*1, v___x_3409_);
v___x_3411_ = l_Repr_addAppParen(v___x_3410_, v_prec_3390_);
return v___x_3411_;
}
v___jp_3412_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; uint8_t v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3414_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__7));
lean_inc(v___y_3413_);
v___x_3415_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___y_3413_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = 0;
v___x_3417_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set_uint8(v___x_3417_, sizeof(void*)*1, v___x_3416_);
v___x_3418_ = l_Repr_addAppParen(v___x_3417_, v_prec_3390_);
return v___x_3418_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr___boxed(lean_object* v_x_3435_, lean_object* v_prec_3436_){
_start:
{
uint8_t v_x_221__boxed_3437_; lean_object* v_res_3438_; 
v_x_221__boxed_3437_ = lean_unbox(v_x_3435_);
v_res_3438_ = l_IO_FS_instReprFileType_repr(v_x_221__boxed_3437_, v_prec_3436_);
lean_dec(v_prec_3436_);
return v_res_3438_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instBEqFileType_beq(uint8_t v_x_3441_, uint8_t v_y_3442_){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; 
v___x_3443_ = lean_box(v_x_3441_);
v___x_3444_ = lean_obj_tag_nat(v___x_3443_);
lean_dec(v___x_3443_);
v___x_3445_ = lean_box(v_y_3442_);
v___x_3446_ = lean_obj_tag_nat(v___x_3445_);
lean_dec(v___x_3445_);
v___x_3447_ = lean_nat_dec_eq(v___x_3444_, v___x_3446_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType_beq___boxed(lean_object* v_x_3448_, lean_object* v_y_3449_){
_start:
{
uint8_t v_x_24__boxed_3450_; uint8_t v_y_25__boxed_3451_; uint8_t v_res_3452_; lean_object* v_r_3453_; 
v_x_24__boxed_3450_ = lean_unbox(v_x_3448_);
v_y_25__boxed_3451_ = lean_unbox(v_y_3449_);
v_res_3452_ = l_IO_FS_instBEqFileType_beq(v_x_24__boxed_3450_, v_y_25__boxed_3451_);
v_r_3453_ = lean_box(v_res_3452_);
return v_r_3453_;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = lean_unsigned_to_nat(7u);
v___x_3466_ = lean_nat_to_int(v___x_3465_);
return v___x_3466_;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3470_ = lean_unsigned_to_nat(0u);
v___x_3471_ = lean_nat_to_int(v___x_3470_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object* v_x_3472_){
_start:
{
lean_object* v_sec_3473_; uint32_t v_nsec_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___y_3479_; lean_object* v___x_3505_; lean_object* v___x_3506_; uint8_t v___x_3507_; 
v_sec_3473_ = lean_ctor_get(v_x_3472_, 0);
v_nsec_3474_ = lean_ctor_get_uint32(v_x_3472_, sizeof(void*)*1);
v___x_3475_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3476_ = ((lean_object*)(l_IO_FS_instReprSystemTime_repr___redArg___closed__3));
v___x_3477_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__4, &l_IO_FS_instReprSystemTime_repr___redArg___closed__4_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4);
v___x_3505_ = lean_unsigned_to_nat(0u);
v___x_3506_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__7, &l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7);
v___x_3507_ = lean_int_dec_lt(v_sec_3473_, v___x_3506_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = l_Int_repr(v_sec_3473_);
v___x_3509_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
v___y_3479_ = v___x_3509_;
goto v___jp_3478_;
}
else
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3510_ = l_Int_repr(v_sec_3473_);
v___x_3511_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
v___x_3512_ = l_Repr_addAppParen(v___x_3511_, v___x_3505_);
v___y_3479_ = v___x_3512_;
goto v___jp_3478_;
}
v___jp_3478_:
{
lean_object* v___x_3480_; uint8_t v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3480_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3477_);
lean_ctor_set(v___x_3480_, 1, v___y_3479_);
v___x_3481_ = 0;
v___x_3482_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3482_, 0, v___x_3480_);
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*1, v___x_3481_);
v___x_3483_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3476_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3483_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = lean_box(1);
v___x_3487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3485_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = ((lean_object*)(l_IO_FS_instReprSystemTime_repr___redArg___closed__6));
v___x_3489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3487_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v___x_3475_);
v___x_3491_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3492_ = lean_uint32_to_nat(v_nsec_3474_);
v___x_3493_ = l_Nat_reprFast(v___x_3492_);
v___x_3494_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
v___x_3495_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3491_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
lean_ctor_set_uint8(v___x_3496_, sizeof(void*)*1, v___x_3481_);
v___x_3497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3490_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3499_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v___x_3497_);
v___x_3501_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3500_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3498_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
v___x_3504_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*1, v___x_3481_);
return v___x_3504_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg___boxed(lean_object* v_x_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_3513_);
lean_dec_ref(v_x_3513_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr(lean_object* v_x_3515_, lean_object* v_prec_3516_){
_start:
{
lean_object* v___x_3517_; 
v___x_3517_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_3515_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___boxed(lean_object* v_x_3518_, lean_object* v_prec_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_IO_FS_instReprSystemTime_repr(v_x_3518_, v_prec_3519_);
lean_dec(v_prec_3519_);
lean_dec_ref(v_x_3518_);
return v_res_3520_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instBEqSystemTime_beq(lean_object* v_x_3523_, lean_object* v_x_3524_){
_start:
{
lean_object* v_sec_3525_; uint32_t v_nsec_3526_; lean_object* v_sec_3527_; uint32_t v_nsec_3528_; uint8_t v___x_3529_; 
v_sec_3525_ = lean_ctor_get(v_x_3523_, 0);
v_nsec_3526_ = lean_ctor_get_uint32(v_x_3523_, sizeof(void*)*1);
v_sec_3527_ = lean_ctor_get(v_x_3524_, 0);
v_nsec_3528_ = lean_ctor_get_uint32(v_x_3524_, sizeof(void*)*1);
v___x_3529_ = lean_int_dec_eq(v_sec_3525_, v_sec_3527_);
if (v___x_3529_ == 0)
{
return v___x_3529_;
}
else
{
uint8_t v___x_3530_; 
v___x_3530_ = lean_uint32_dec_eq(v_nsec_3526_, v_nsec_3528_);
return v___x_3530_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime_beq___boxed(lean_object* v_x_3531_, lean_object* v_x_3532_){
_start:
{
uint8_t v_res_3533_; lean_object* v_r_3534_; 
v_res_3533_ = l_IO_FS_instBEqSystemTime_beq(v_x_3531_, v_x_3532_);
lean_dec_ref(v_x_3532_);
lean_dec_ref(v_x_3531_);
v_r_3534_ = lean_box(v_res_3533_);
return v_r_3534_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object* v_x_3537_, lean_object* v_x_3538_){
_start:
{
lean_object* v_sec_3539_; uint32_t v_nsec_3540_; lean_object* v_sec_3541_; uint32_t v_nsec_3542_; uint8_t v___x_3543_; 
v_sec_3539_ = lean_ctor_get(v_x_3537_, 0);
v_nsec_3540_ = lean_ctor_get_uint32(v_x_3537_, sizeof(void*)*1);
v_sec_3541_ = lean_ctor_get(v_x_3538_, 0);
v_nsec_3542_ = lean_ctor_get_uint32(v_x_3538_, sizeof(void*)*1);
v___x_3543_ = lean_int_dec_lt(v_sec_3539_, v_sec_3541_);
if (v___x_3543_ == 0)
{
uint8_t v___x_3544_; 
v___x_3544_ = lean_int_dec_eq(v_sec_3539_, v_sec_3541_);
if (v___x_3544_ == 0)
{
uint8_t v___x_3545_; 
v___x_3545_ = 2;
return v___x_3545_;
}
else
{
uint8_t v___x_3546_; 
v___x_3546_ = lean_uint32_dec_lt(v_nsec_3540_, v_nsec_3542_);
if (v___x_3546_ == 0)
{
uint8_t v___x_3547_; 
v___x_3547_ = lean_uint32_dec_eq(v_nsec_3540_, v_nsec_3542_);
if (v___x_3547_ == 0)
{
uint8_t v___x_3548_; 
v___x_3548_ = 2;
return v___x_3548_;
}
else
{
uint8_t v___x_3549_; 
v___x_3549_ = 1;
return v___x_3549_;
}
}
else
{
uint8_t v___x_3550_; 
v___x_3550_ = 0;
return v___x_3550_;
}
}
}
else
{
uint8_t v___x_3551_; 
v___x_3551_ = 0;
return v___x_3551_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime_ord___boxed(lean_object* v_x_3552_, lean_object* v_x_3553_){
_start:
{
uint8_t v_res_3554_; lean_object* v_r_3555_; 
v_res_3554_ = l_IO_FS_instOrdSystemTime_ord(v_x_3552_, v_x_3553_);
lean_dec_ref(v_x_3553_);
lean_dec_ref(v_x_3552_);
v_r_3555_ = lean_box(v_res_3554_);
return v_r_3555_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default___closed__0(void){
_start:
{
uint32_t v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = 0;
v___x_3559_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__7, &l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7);
v___x_3560_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
lean_ctor_set_uint32(v___x_3560_, sizeof(void*)*1, v___x_3558_);
return v___x_3560_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default(void){
_start:
{
lean_object* v___x_3561_; 
v___x_3561_ = lean_obj_once(&l_IO_FS_instInhabitedSystemTime_default___closed__0, &l_IO_FS_instInhabitedSystemTime_default___closed__0_once, _init_l_IO_FS_instInhabitedSystemTime_default___closed__0);
return v___x_3561_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime(void){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = l_IO_FS_instInhabitedSystemTime_default;
return v___x_3562_;
}
}
static lean_object* _init_l_IO_FS_instLTSystemTime(void){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_box(0);
return v___x_3563_;
}
}
static lean_object* _init_l_IO_FS_instLESystemTime(void){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = lean_box(0);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg(lean_object* v_x_3586_){
_start:
{
lean_object* v_accessed_3587_; lean_object* v_modified_3588_; uint64_t v_byteSize_3589_; uint8_t v_type_3590_; uint64_t v_numLinks_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v_accessed_3587_ = lean_ctor_get(v_x_3586_, 0);
v_modified_3588_ = lean_ctor_get(v_x_3586_, 1);
v_byteSize_3589_ = lean_ctor_get_uint64(v_x_3586_, sizeof(void*)*2);
v_type_3590_ = lean_ctor_get_uint8(v_x_3586_, sizeof(void*)*2 + 16);
v_numLinks_3591_ = lean_ctor_get_uint64(v_x_3586_, sizeof(void*)*2 + 8);
v___x_3592_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3593_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__3));
v___x_3594_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__14, &l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14);
v___x_3595_ = lean_unsigned_to_nat(0u);
v___x_3596_ = l_IO_FS_instReprSystemTime_repr___redArg(v_accessed_3587_);
v___x_3597_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3594_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = 0;
v___x_3599_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3599_, 0, v___x_3597_);
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*1, v___x_3598_);
v___x_3600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3593_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
v___x_3601_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3600_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = lean_box(1);
v___x_3604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3602_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__5));
v___x_3606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3604_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
lean_ctor_set(v___x_3607_, 1, v___x_3592_);
v___x_3608_ = l_IO_FS_instReprSystemTime_repr___redArg(v_modified_3588_);
v___x_3609_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3594_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
lean_ctor_set_uint8(v___x_3610_, sizeof(void*)*1, v___x_3598_);
v___x_3611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3607_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
lean_ctor_set(v___x_3612_, 1, v___x_3601_);
v___x_3613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
lean_ctor_set(v___x_3613_, 1, v___x_3603_);
v___x_3614_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__7));
v___x_3615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3613_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
lean_ctor_set(v___x_3616_, 1, v___x_3592_);
v___x_3617_ = lean_uint64_to_nat(v_byteSize_3589_);
v___x_3618_ = l_Nat_reprFast(v___x_3617_);
v___x_3619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
v___x_3620_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3594_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
lean_ctor_set_uint8(v___x_3621_, sizeof(void*)*1, v___x_3598_);
v___x_3622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3616_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
lean_ctor_set(v___x_3623_, 1, v___x_3601_);
v___x_3624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
lean_ctor_set(v___x_3624_, 1, v___x_3603_);
v___x_3625_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__9));
v___x_3626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3624_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
lean_ctor_set(v___x_3627_, 1, v___x_3592_);
v___x_3628_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3629_ = l_IO_FS_instReprFileType_repr(v_type_3590_, v___x_3595_);
v___x_3630_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3628_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
lean_ctor_set_uint8(v___x_3631_, sizeof(void*)*1, v___x_3598_);
v___x_3632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3627_);
lean_ctor_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
lean_ctor_set(v___x_3633_, 1, v___x_3601_);
v___x_3634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
lean_ctor_set(v___x_3634_, 1, v___x_3603_);
v___x_3635_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__11));
v___x_3636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3634_);
lean_ctor_set(v___x_3636_, 1, v___x_3635_);
v___x_3637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3636_);
lean_ctor_set(v___x_3637_, 1, v___x_3592_);
v___x_3638_ = lean_uint64_to_nat(v_numLinks_3591_);
v___x_3639_ = l_Nat_reprFast(v___x_3638_);
v___x_3640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3639_);
v___x_3641_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3594_);
lean_ctor_set(v___x_3641_, 1, v___x_3640_);
v___x_3642_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
lean_ctor_set_uint8(v___x_3642_, sizeof(void*)*1, v___x_3598_);
v___x_3643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3637_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
v___x_3644_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3645_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
lean_ctor_set(v___x_3646_, 1, v___x_3643_);
v___x_3647_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3646_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3644_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
lean_ctor_set_uint8(v___x_3650_, sizeof(void*)*1, v___x_3598_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg___boxed(lean_object* v_x_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_3651_);
lean_dec_ref(v_x_3651_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr(lean_object* v_x_3653_, lean_object* v_prec_3654_){
_start:
{
lean_object* v___x_3655_; 
v___x_3655_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_3653_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___boxed(lean_object* v_x_3656_, lean_object* v_prec_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_IO_FS_instReprMetadata_repr(v_x_3656_, v_prec_3657_);
lean_dec(v_prec_3657_);
lean_dec_ref(v_x_3656_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object* v_a_00___x40___internal___hyg_3663_, lean_object* v_a_00___x40___internal___hyg_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = lean_io_read_dir(v_a_00___x40___internal___hyg_3663_);
lean_dec_ref(v_a_00___x40___internal___hyg_3663_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object* v_a_00___x40___internal___hyg_3668_, lean_object* v_a_00___x40___internal___hyg_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = lean_io_metadata(v_a_00___x40___internal___hyg_3668_);
lean_dec_ref(v_a_00___x40___internal___hyg_3668_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_symlinkMetadata___boxed(lean_object* v_a_00___x40___internal___hyg_3673_, lean_object* v_a_00___x40___internal___hyg_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = lean_io_symlink_metadata(v_a_00___x40___internal___hyg_3673_);
lean_dec_ref(v_a_00___x40___internal___hyg_3673_);
return v_res_3675_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isDir(lean_object* v_p_3676_){
_start:
{
lean_object* v___x_3678_; 
v___x_3678_ = lean_io_metadata(v_p_3676_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; uint8_t v_type_3680_; uint8_t v___x_3681_; uint8_t v___x_3682_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v___x_3678_, 1);
v_type_3680_ = lean_ctor_get_uint8(v_a_3679_, sizeof(void*)*2 + 16);
lean_dec(v_a_3679_);
v___x_3681_ = 0;
v___x_3682_ = l_IO_FS_instBEqFileType_beq(v_type_3680_, v___x_3681_);
return v___x_3682_;
}
else
{
uint8_t v___x_3683_; 
lean_dec_ref_known(v___x_3678_, 1);
v___x_3683_ = 0;
return v___x_3683_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object* v_p_3684_, lean_object* v_a_3685_){
_start:
{
uint8_t v_res_3686_; lean_object* v_r_3687_; 
v_res_3686_ = l_System_FilePath_isDir(v_p_3684_);
lean_dec_ref(v_p_3684_);
v_r_3687_ = lean_box(v_res_3686_);
return v_r_3687_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_pathExists(lean_object* v_p_3688_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = lean_io_metadata(v_p_3688_);
if (lean_obj_tag(v___x_3690_) == 0)
{
uint8_t v___x_3691_; 
lean_dec_ref_known(v___x_3690_, 1);
v___x_3691_ = 1;
return v___x_3691_;
}
else
{
uint8_t v___x_3692_; 
lean_dec_ref_known(v___x_3690_, 1);
v___x_3692_ = 0;
return v___x_3692_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object* v_p_3693_, lean_object* v_a_3694_){
_start:
{
uint8_t v_res_3695_; lean_object* v_r_3696_; 
v_res_3695_ = l_System_FilePath_pathExists(v_p_3693_);
lean_dec_ref(v_p_3693_);
v_r_3696_ = lean_box(v_res_3695_);
return v_r_3696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(lean_object* v_enter_3697_, lean_object* v_p_3698_, lean_object* v_as_3699_, size_t v_sz_3700_, size_t v_i_3701_, lean_object* v_b_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v_a_3706_; lean_object* v_snd_3707_; uint8_t v___x_3711_; 
v___x_3711_ = lean_usize_dec_lt(v_i_3701_, v_sz_3700_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
lean_dec_ref(v_p_3698_);
lean_dec_ref(v_enter_3697_);
v___x_3712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3712_, 0, v_b_3702_);
lean_ctor_set(v___x_3712_, 1, v___y_3703_);
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
return v___x_3713_;
}
else
{
lean_object* v___x_3714_; lean_object* v_a_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3714_ = lean_box(0);
v_a_3715_ = lean_array_uget_borrowed(v_as_3699_, v_i_3701_);
lean_inc(v_a_3715_);
v___x_3716_ = l_IO_FS_DirEntry_path(v_a_3715_);
lean_inc_ref(v___x_3716_);
v___x_3717_ = lean_array_push(v___y_3703_, v___x_3716_);
v___x_3718_ = lean_io_metadata(v___x_3716_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; uint8_t v_type_3720_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref_known(v___x_3718_, 1);
v_type_3720_ = lean_ctor_get_uint8(v_a_3719_, sizeof(void*)*2 + 16);
lean_dec(v_a_3719_);
switch(v_type_3720_)
{
case 2:
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_io_realpath(v___x_3716_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; uint8_t v___x_3723_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3721_, 1);
v___x_3723_ = l_System_FilePath_isDir(v_a_3722_);
if (v___x_3723_ == 0)
{
lean_dec(v_a_3722_);
v_a_3706_ = v___x_3714_;
v_snd_3707_ = v___x_3717_;
goto v___jp_3705_;
}
else
{
lean_object* v___x_3724_; 
lean_inc_ref(v_enter_3697_);
lean_inc_ref(v_p_3698_);
v___x_3724_ = lean_apply_2(v_enter_3697_, v_p_3698_, lean_box(0));
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; uint8_t v___x_3726_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref_known(v___x_3724_, 1);
v___x_3726_ = lean_unbox(v_a_3725_);
lean_dec(v_a_3725_);
if (v___x_3726_ == 0)
{
lean_dec(v_a_3722_);
v_a_3706_ = v___x_3714_;
v_snd_3707_ = v___x_3717_;
goto v___jp_3705_;
}
else
{
lean_object* v___x_3727_; 
lean_inc_ref(v_enter_3697_);
v___x_3727_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3697_, v_a_3722_, v___x_3717_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v_snd_3729_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3727_, 1);
v_snd_3729_ = lean_ctor_get(v_a_3728_, 1);
lean_inc(v_snd_3729_);
lean_dec(v_a_3728_);
v_a_3706_ = v___x_3714_;
v_snd_3707_ = v_snd_3729_;
goto v___jp_3705_;
}
else
{
lean_dec_ref(v_p_3698_);
lean_dec_ref(v_enter_3697_);
return v___x_3727_;
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec(v_a_3722_);
lean_dec_ref(v___x_3717_);
lean_dec_ref(v_p_3698_);
lean_dec_ref(v_enter_3697_);
v_a_3730_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3724_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3724_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec_ref(v___x_3717_);
lean_dec_ref(v_p_3698_);
lean_dec_ref(v_enter_3697_);
v_a_3738_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3721_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3721_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
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
case 0:
{
lean_object* v___x_3746_; 
lean_inc_ref(v_enter_3697_);
v___x_3746_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3697_, v___x_3716_, v___x_3717_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v_snd_3748_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3746_, 1);
v_snd_3748_ = lean_ctor_get(v_a_3747_, 1);
lean_inc(v_snd_3748_);
lean_dec(v_a_3747_);
v_a_3706_ = v___x_3714_;
v_snd_3707_ = v_snd_3748_;
goto v___jp_3705_;
}
else
{
lean_dec_ref(v_p_3698_);
lean_dec_ref(v_enter_3697_);
return v___x_3746_;
}
}
default: 
{
lean_dec_ref(v___x_3716_);
v_a_3706_ = v___x_3714_;
v_snd_3707_ = v___x_3717_;
goto v___jp_3705_;
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec_ref(v___x_3716_);
v_a_3749_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3718_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3718_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
if (lean_obj_tag(v_a_3749_) == 11)
{
lean_dec_ref_known(v_a_3749_, 2);
lean_del_object(v___x_3751_);
v_a_3706_ = v___x_3714_;
v_snd_3707_ = v___x_3717_;
goto v___jp_3705_;
}
else
{
lean_object* v___x_3754_; 
lean_dec_ref(v___x_3717_);
lean_dec_ref(v_p_3698_);
lean_dec_ref(v_enter_3697_);
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
v___jp_3705_:
{
size_t v___x_3708_; size_t v___x_3709_; 
v___x_3708_ = ((size_t)1ULL);
v___x_3709_ = lean_usize_add(v_i_3701_, v___x_3708_);
v_i_3701_ = v___x_3709_;
v_b_3702_ = v_a_3706_;
v___y_3703_ = v_snd_3707_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go(lean_object* v_enter_3757_, lean_object* v_p_3758_, lean_object* v_a_3759_){
_start:
{
lean_object* v___x_3761_; 
lean_inc_ref(v_enter_3757_);
lean_inc_ref(v_p_3758_);
v___x_3761_ = lean_apply_2(v_enter_3757_, v_p_3758_, lean_box(0));
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3803_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3764_ = v___x_3761_;
v_isShared_3765_ = v_isSharedCheck_3803_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3761_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3803_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
uint8_t v___x_3766_; 
v___x_3766_ = lean_unbox(v_a_3762_);
lean_dec(v_a_3762_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3770_; 
lean_dec_ref(v_p_3758_);
lean_dec_ref(v_enter_3757_);
v___x_3767_ = lean_box(0);
v___x_3768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
lean_ctor_set(v___x_3768_, 1, v_a_3759_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 0, v___x_3768_);
v___x_3770_ = v___x_3764_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
else
{
lean_object* v___x_3772_; 
lean_del_object(v___x_3764_);
v___x_3772_ = lean_io_read_dir(v_p_3758_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_a_3773_; lean_object* v___x_3774_; size_t v_sz_3775_; size_t v___x_3776_; lean_object* v___x_3777_; 
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_a_3773_);
lean_dec_ref_known(v___x_3772_, 1);
v___x_3774_ = lean_box(0);
v_sz_3775_ = lean_array_size(v_a_3773_);
v___x_3776_ = ((size_t)0ULL);
v___x_3777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_3757_, v_p_3758_, v_a_3773_, v_sz_3775_, v___x_3776_, v___x_3774_, v_a_3759_);
lean_dec(v_a_3773_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3794_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3780_ = v___x_3777_;
v_isShared_3781_ = v_isSharedCheck_3794_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3777_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3794_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v_snd_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3792_; 
v_snd_3782_ = lean_ctor_get(v_a_3778_, 1);
v_isSharedCheck_3792_ = !lean_is_exclusive(v_a_3778_);
if (v_isSharedCheck_3792_ == 0)
{
lean_object* v_unused_3793_; 
v_unused_3793_ = lean_ctor_get(v_a_3778_, 0);
lean_dec(v_unused_3793_);
v___x_3784_ = v_a_3778_;
v_isShared_3785_ = v_isSharedCheck_3792_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_snd_3782_);
lean_dec(v_a_3778_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3792_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 0, v___x_3774_);
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v_snd_3782_);
v___x_3787_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
lean_object* v___x_3789_; 
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 0, v___x_3787_);
v___x_3789_ = v___x_3780_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3787_);
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
return v___x_3777_;
}
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
lean_dec_ref(v_a_3759_);
lean_dec_ref(v_p_3758_);
lean_dec_ref(v_enter_3757_);
v_a_3795_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3772_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3772_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
lean_dec_ref(v_a_3759_);
lean_dec_ref(v_p_3758_);
lean_dec_ref(v_enter_3757_);
v_a_3804_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3761_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3761_);
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
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go___boxed(lean_object* v_enter_3812_, lean_object* v_p_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3812_, v_p_3813_, v_a_3814_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0___boxed(lean_object* v_enter_3817_, lean_object* v_p_3818_, lean_object* v_as_3819_, lean_object* v_sz_3820_, lean_object* v_i_3821_, lean_object* v_b_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
size_t v_sz_boxed_3825_; size_t v_i_boxed_3826_; lean_object* v_res_3827_; 
v_sz_boxed_3825_ = lean_unbox_usize(v_sz_3820_);
lean_dec(v_sz_3820_);
v_i_boxed_3826_ = lean_unbox_usize(v_i_3821_);
lean_dec(v_i_3821_);
v_res_3827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_3817_, v_p_3818_, v_as_3819_, v_sz_boxed_3825_, v_i_boxed_3826_, v_b_3822_, v___y_3823_);
lean_dec_ref(v_as_3819_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object* v_p_3828_, lean_object* v_enter_3829_){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_3832_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3829_, v_p_3828_, v___x_3831_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3841_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3835_ = v___x_3832_;
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3832_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v_snd_3837_; lean_object* v___x_3839_; 
v_snd_3837_ = lean_ctor_get(v_a_3833_, 1);
lean_inc(v_snd_3837_);
lean_dec(v_a_3833_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v_snd_3837_);
v___x_3839_ = v___x_3835_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_snd_3837_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
v_a_3842_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3832_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3832_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir___boxed(lean_object* v_p_3850_, lean_object* v_enter_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l_System_FilePath_walkDir(v_p_3850_, v_enter_3851_);
return v_res_3853_;
}
}
static lean_object* _init_l_IO_FS_readBinFile___closed__0(void){
_start:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = lean_unsigned_to_nat(0u);
v___x_3855_ = lean_mk_empty_byte_array(v___x_3854_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object* v_fname_3856_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = lean_io_metadata(v_fname_3856_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; uint64_t v_byteSize_3860_; size_t v___x_3861_; uint8_t v___x_3862_; lean_object* v___x_3863_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref_known(v___x_3858_, 1);
v_byteSize_3860_ = lean_ctor_get_uint64(v_a_3859_, sizeof(void*)*2);
lean_dec(v_a_3859_);
v___x_3861_ = lean_uint64_to_usize(v_byteSize_3860_);
v___x_3862_ = 0;
v___x_3863_ = lean_io_prim_handle_mk(v_fname_3856_, v___x_3862_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; size_t v___x_3865_; uint8_t v___x_3866_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v___x_3863_, 1);
v___x_3865_ = ((size_t)0ULL);
v___x_3866_ = lean_usize_dec_lt(v___x_3865_, v___x_3861_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = lean_obj_once(&l_IO_FS_readBinFile___closed__0, &l_IO_FS_readBinFile___closed__0_once, _init_l_IO_FS_readBinFile___closed__0);
v___x_3868_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_a_3864_, v___x_3867_);
lean_dec(v_a_3864_);
return v___x_3868_;
}
else
{
lean_object* v___x_3869_; 
v___x_3869_ = lean_io_prim_handle_read(v_a_3864_, v___x_3861_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v___x_3871_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3869_, 1);
v___x_3871_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_a_3864_, v_a_3870_);
lean_dec(v_a_3864_);
return v___x_3871_;
}
else
{
lean_dec(v_a_3864_);
return v___x_3869_;
}
}
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
v_a_3872_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3863_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3863_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
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
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
v_a_3880_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3858_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3858_);
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
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object* v_fname_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_IO_FS_readBinFile(v_fname_3888_);
lean_dec_ref(v_fname_3888_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object* v_fname_3893_){
_start:
{
lean_object* v___x_3895_; 
v___x_3895_ = l_IO_FS_readBinFile(v_fname_3893_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3913_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3898_ = v___x_3895_;
v_isShared_3899_ = v_isSharedCheck_3913_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3895_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3913_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
uint8_t v___x_3900_; 
v___x_3900_ = lean_string_validate_utf8(v_a_3896_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3907_; 
lean_dec(v_a_3896_);
v___x_3901_ = ((lean_object*)(l_IO_FS_readFile___closed__0));
v___x_3902_ = lean_string_append(v___x_3901_, v_fname_3893_);
v___x_3903_ = ((lean_object*)(l_IO_FS_readFile___closed__1));
v___x_3904_ = lean_string_append(v___x_3902_, v___x_3903_);
v___x_3905_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set_tag(v___x_3898_, 1);
lean_ctor_set(v___x_3898_, 0, v___x_3905_);
v___x_3907_ = v___x_3898_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
else
{
lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3909_ = lean_string_from_utf8_unchecked(v_a_3896_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 0, v___x_3909_);
v___x_3911_ = v___x_3898_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
v_a_3914_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3895_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3895_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object* v_fname_3922_, lean_object* v_a_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l_IO_FS_readFile(v_fname_3922_);
lean_dec_ref(v_fname_3922_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0(lean_object* v_x_3925_){
_start:
{
lean_object* v_fst_3926_; 
v_fst_3926_ = lean_ctor_get(v_x_3925_, 0);
lean_inc(v_fst_3926_);
return v_fst_3926_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0___boxed(lean_object* v_x_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_IO_withStdin___redArg___lam__0(v_x_3927_);
lean_dec_ref(v_x_3927_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1(lean_object* v___x_3929_, lean_object* v_x_3930_){
_start:
{
lean_inc(v___x_3929_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1___boxed(lean_object* v___x_3931_, lean_object* v_x_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_IO_withStdin___redArg___lam__1(v___x_3931_, v_x_3932_);
lean_dec(v_x_3932_);
lean_dec(v___x_3931_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__2(lean_object* v_toFunctor_3934_, lean_object* v_inst_3935_, lean_object* v_inst_3936_, lean_object* v_x_3937_, lean_object* v___f_3938_, lean_object* v_prev_3939_){
_start:
{
lean_object* v_map_3940_; lean_object* v_mapConst_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___f_3946_; lean_object* v_y_3947_; lean_object* v___x_3948_; 
v_map_3940_ = lean_ctor_get(v_toFunctor_3934_, 0);
lean_inc(v_map_3940_);
v_mapConst_3941_ = lean_ctor_get(v_toFunctor_3934_, 1);
lean_inc(v_mapConst_3941_);
lean_dec_ref(v_toFunctor_3934_);
v___x_3942_ = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(v___x_3942_, 0, v_prev_3939_);
v___x_3943_ = lean_apply_2(v_inst_3935_, lean_box(0), v___x_3942_);
v___x_3944_ = lean_box(0);
v___x_3945_ = lean_apply_4(v_mapConst_3941_, lean_box(0), lean_box(0), v___x_3944_, v___x_3943_);
v___f_3946_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3946_, 0, v___x_3945_);
v_y_3947_ = lean_apply_4(v_inst_3936_, lean_box(0), lean_box(0), v_x_3937_, v___f_3946_);
v___x_3948_ = lean_apply_4(v_map_3940_, lean_box(0), lean_box(0), v___f_3938_, v_y_3947_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg(lean_object* v_inst_3950_, lean_object* v_inst_3951_, lean_object* v_inst_3952_, lean_object* v_h_3953_, lean_object* v_x_3954_){
_start:
{
lean_object* v_toApplicative_3955_; lean_object* v_toBind_3956_; lean_object* v_toFunctor_3957_; lean_object* v___f_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___f_3961_; lean_object* v___x_3962_; 
v_toApplicative_3955_ = lean_ctor_get(v_inst_3950_, 0);
lean_inc_ref(v_toApplicative_3955_);
v_toBind_3956_ = lean_ctor_get(v_inst_3950_, 1);
lean_inc(v_toBind_3956_);
lean_dec_ref(v_inst_3950_);
v_toFunctor_3957_ = lean_ctor_get(v_toApplicative_3955_, 0);
lean_inc_ref(v_toFunctor_3957_);
lean_dec_ref(v_toApplicative_3955_);
v___f_3958_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3959_ = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(v___x_3959_, 0, v_h_3953_);
lean_inc(v_inst_3952_);
v___x_3960_ = lean_apply_2(v_inst_3952_, lean_box(0), v___x_3959_);
v___f_3961_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3961_, 0, v_toFunctor_3957_);
lean_closure_set(v___f_3961_, 1, v_inst_3952_);
lean_closure_set(v___f_3961_, 2, v_inst_3951_);
lean_closure_set(v___f_3961_, 3, v_x_3954_);
lean_closure_set(v___f_3961_, 4, v___f_3958_);
v___x_3962_ = lean_apply_4(v_toBind_3956_, lean_box(0), lean_box(0), v___x_3960_, v___f_3961_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object* v_m_3963_, lean_object* v_00_u03b1_3964_, lean_object* v_inst_3965_, lean_object* v_inst_3966_, lean_object* v_inst_3967_, lean_object* v_h_3968_, lean_object* v_x_3969_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_IO_withStdin___redArg(v_inst_3965_, v_inst_3966_, v_inst_3967_, v_h_3968_, v_x_3969_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg___lam__2(lean_object* v_toFunctor_3971_, lean_object* v_inst_3972_, lean_object* v_inst_3973_, lean_object* v_x_3974_, lean_object* v___f_3975_, lean_object* v_prev_3976_){
_start:
{
lean_object* v_map_3977_; lean_object* v_mapConst_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___f_3983_; lean_object* v_y_3984_; lean_object* v___x_3985_; 
v_map_3977_ = lean_ctor_get(v_toFunctor_3971_, 0);
lean_inc(v_map_3977_);
v_mapConst_3978_ = lean_ctor_get(v_toFunctor_3971_, 1);
lean_inc(v_mapConst_3978_);
lean_dec_ref(v_toFunctor_3971_);
v___x_3979_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_3979_, 0, v_prev_3976_);
v___x_3980_ = lean_apply_2(v_inst_3972_, lean_box(0), v___x_3979_);
v___x_3981_ = lean_box(0);
v___x_3982_ = lean_apply_4(v_mapConst_3978_, lean_box(0), lean_box(0), v___x_3981_, v___x_3980_);
v___f_3983_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3983_, 0, v___x_3982_);
v_y_3984_ = lean_apply_4(v_inst_3973_, lean_box(0), lean_box(0), v_x_3974_, v___f_3983_);
v___x_3985_ = lean_apply_4(v_map_3977_, lean_box(0), lean_box(0), v___f_3975_, v_y_3984_);
return v___x_3985_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg(lean_object* v_inst_3986_, lean_object* v_inst_3987_, lean_object* v_inst_3988_, lean_object* v_h_3989_, lean_object* v_x_3990_){
_start:
{
lean_object* v_toApplicative_3991_; lean_object* v_toBind_3992_; lean_object* v_toFunctor_3993_; lean_object* v___f_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___f_3997_; lean_object* v___x_3998_; 
v_toApplicative_3991_ = lean_ctor_get(v_inst_3986_, 0);
lean_inc_ref(v_toApplicative_3991_);
v_toBind_3992_ = lean_ctor_get(v_inst_3986_, 1);
lean_inc(v_toBind_3992_);
lean_dec_ref(v_inst_3986_);
v_toFunctor_3993_ = lean_ctor_get(v_toApplicative_3991_, 0);
lean_inc_ref(v_toFunctor_3993_);
lean_dec_ref(v_toApplicative_3991_);
v___f_3994_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3995_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_3995_, 0, v_h_3989_);
lean_inc(v_inst_3988_);
v___x_3996_ = lean_apply_2(v_inst_3988_, lean_box(0), v___x_3995_);
v___f_3997_ = lean_alloc_closure((void*)(l_IO_withStdout___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3997_, 0, v_toFunctor_3993_);
lean_closure_set(v___f_3997_, 1, v_inst_3988_);
lean_closure_set(v___f_3997_, 2, v_inst_3987_);
lean_closure_set(v___f_3997_, 3, v_x_3990_);
lean_closure_set(v___f_3997_, 4, v___f_3994_);
v___x_3998_ = lean_apply_4(v_toBind_3992_, lean_box(0), lean_box(0), v___x_3996_, v___f_3997_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object* v_m_3999_, lean_object* v_00_u03b1_4000_, lean_object* v_inst_4001_, lean_object* v_inst_4002_, lean_object* v_inst_4003_, lean_object* v_h_4004_, lean_object* v_x_4005_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_IO_withStdout___redArg(v_inst_4001_, v_inst_4002_, v_inst_4003_, v_h_4004_, v_x_4005_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg___lam__2(lean_object* v_toFunctor_4007_, lean_object* v_inst_4008_, lean_object* v_inst_4009_, lean_object* v_x_4010_, lean_object* v___f_4011_, lean_object* v_prev_4012_){
_start:
{
lean_object* v_map_4013_; lean_object* v_mapConst_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___f_4019_; lean_object* v_y_4020_; lean_object* v___x_4021_; 
v_map_4013_ = lean_ctor_get(v_toFunctor_4007_, 0);
lean_inc(v_map_4013_);
v_mapConst_4014_ = lean_ctor_get(v_toFunctor_4007_, 1);
lean_inc(v_mapConst_4014_);
lean_dec_ref(v_toFunctor_4007_);
v___x_4015_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_4015_, 0, v_prev_4012_);
v___x_4016_ = lean_apply_2(v_inst_4008_, lean_box(0), v___x_4015_);
v___x_4017_ = lean_box(0);
v___x_4018_ = lean_apply_4(v_mapConst_4014_, lean_box(0), lean_box(0), v___x_4017_, v___x_4016_);
v___f_4019_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4019_, 0, v___x_4018_);
v_y_4020_ = lean_apply_4(v_inst_4009_, lean_box(0), lean_box(0), v_x_4010_, v___f_4019_);
v___x_4021_ = lean_apply_4(v_map_4013_, lean_box(0), lean_box(0), v___f_4011_, v_y_4020_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg(lean_object* v_inst_4022_, lean_object* v_inst_4023_, lean_object* v_inst_4024_, lean_object* v_h_4025_, lean_object* v_x_4026_){
_start:
{
lean_object* v_toApplicative_4027_; lean_object* v_toBind_4028_; lean_object* v_toFunctor_4029_; lean_object* v___f_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___f_4033_; lean_object* v___x_4034_; 
v_toApplicative_4027_ = lean_ctor_get(v_inst_4022_, 0);
lean_inc_ref(v_toApplicative_4027_);
v_toBind_4028_ = lean_ctor_get(v_inst_4022_, 1);
lean_inc(v_toBind_4028_);
lean_dec_ref(v_inst_4022_);
v_toFunctor_4029_ = lean_ctor_get(v_toApplicative_4027_, 0);
lean_inc_ref(v_toFunctor_4029_);
lean_dec_ref(v_toApplicative_4027_);
v___f_4030_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4031_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_4031_, 0, v_h_4025_);
lean_inc(v_inst_4024_);
v___x_4032_ = lean_apply_2(v_inst_4024_, lean_box(0), v___x_4031_);
v___f_4033_ = lean_alloc_closure((void*)(l_IO_withStderr___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4033_, 0, v_toFunctor_4029_);
lean_closure_set(v___f_4033_, 1, v_inst_4024_);
lean_closure_set(v___f_4033_, 2, v_inst_4023_);
lean_closure_set(v___f_4033_, 3, v_x_4026_);
lean_closure_set(v___f_4033_, 4, v___f_4030_);
v___x_4034_ = lean_apply_4(v_toBind_4028_, lean_box(0), lean_box(0), v___x_4032_, v___f_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object* v_m_4035_, lean_object* v_00_u03b1_4036_, lean_object* v_inst_4037_, lean_object* v_inst_4038_, lean_object* v_inst_4039_, lean_object* v_h_4040_, lean_object* v_x_4041_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_IO_withStderr___redArg(v_inst_4037_, v_inst_4038_, v_inst_4039_, v_h_4040_, v_x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_IO_print___redArg(lean_object* v_inst_4043_, lean_object* v_s_4044_){
_start:
{
lean_object* v___x_4046_; lean_object* v_putStr_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4046_ = lean_get_stdout();
v_putStr_4047_ = lean_ctor_get(v___x_4046_, 4);
lean_inc_ref(v_putStr_4047_);
lean_dec_ref(v___x_4046_);
v___x_4048_ = lean_apply_1(v_inst_4043_, v_s_4044_);
v___x_4049_ = lean_apply_2(v_putStr_4047_, v___x_4048_, lean_box(0));
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_IO_print___redArg___boxed(lean_object* v_inst_4050_, lean_object* v_s_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_IO_print___redArg(v_inst_4050_, v_s_4051_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_IO_print(lean_object* v_00_u03b1_4054_, lean_object* v_inst_4055_, lean_object* v_s_4056_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_IO_print___redArg(v_inst_4055_, v_s_4056_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_IO_print___boxed(lean_object* v_00_u03b1_4059_, lean_object* v_inst_4060_, lean_object* v_s_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_IO_print(v_00_u03b1_4059_, v_inst_4060_, v_s_4061_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_IO_println___redArg(lean_object* v_inst_4065_, lean_object* v_s_4066_){
_start:
{
lean_object* v___f_4068_; lean_object* v___x_4069_; uint32_t v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___f_4068_ = ((lean_object*)(l_IO_println___redArg___closed__0));
v___x_4069_ = lean_apply_1(v_inst_4065_, v_s_4066_);
v___x_4070_ = 10;
v___x_4071_ = lean_string_push(v___x_4069_, v___x_4070_);
v___x_4072_ = l_IO_print___redArg(v___f_4068_, v___x_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_IO_println___redArg___boxed(lean_object* v_inst_4073_, lean_object* v_s_4074_, lean_object* v_a_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_IO_println___redArg(v_inst_4073_, v_s_4074_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_IO_println(lean_object* v_00_u03b1_4077_, lean_object* v_inst_4078_, lean_object* v_s_4079_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_IO_println___redArg(v_inst_4078_, v_s_4079_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_IO_println___boxed(lean_object* v_00_u03b1_4082_, lean_object* v_inst_4083_, lean_object* v_s_4084_, lean_object* v_a_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_IO_println(v_00_u03b1_4082_, v_inst_4083_, v_s_4084_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg(lean_object* v_inst_4087_, lean_object* v_s_4088_){
_start:
{
lean_object* v___x_4090_; lean_object* v_putStr_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4090_ = lean_get_stderr();
v_putStr_4091_ = lean_ctor_get(v___x_4090_, 4);
lean_inc_ref(v_putStr_4091_);
lean_dec_ref(v___x_4090_);
v___x_4092_ = lean_apply_1(v_inst_4087_, v_s_4088_);
v___x_4093_ = lean_apply_2(v_putStr_4091_, v___x_4092_, lean_box(0));
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg___boxed(lean_object* v_inst_4094_, lean_object* v_s_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l_IO_eprint___redArg(v_inst_4094_, v_s_4095_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint(lean_object* v_00_u03b1_4098_, lean_object* v_inst_4099_, lean_object* v_s_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_IO_eprint___redArg(v_inst_4099_, v_s_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___boxed(lean_object* v_00_u03b1_4103_, lean_object* v_inst_4104_, lean_object* v_s_4105_, lean_object* v_a_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_IO_eprint(v_00_u03b1_4103_, v_inst_4104_, v_s_4105_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg(lean_object* v_inst_4108_, lean_object* v_s_4109_){
_start:
{
lean_object* v___f_4111_; lean_object* v___x_4112_; uint32_t v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___f_4111_ = ((lean_object*)(l_IO_println___redArg___closed__0));
v___x_4112_ = lean_apply_1(v_inst_4108_, v_s_4109_);
v___x_4113_ = 10;
v___x_4114_ = lean_string_push(v___x_4112_, v___x_4113_);
v___x_4115_ = l_IO_eprint___redArg(v___f_4111_, v___x_4114_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg___boxed(lean_object* v_inst_4116_, lean_object* v_s_4117_, lean_object* v_a_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_IO_eprintln___redArg(v_inst_4116_, v_s_4117_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object* v_00_u03b1_4120_, lean_object* v_inst_4121_, lean_object* v_s_4122_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_IO_eprintln___redArg(v_inst_4121_, v_s_4122_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___boxed(lean_object* v_00_u03b1_4125_, lean_object* v_inst_4126_, lean_object* v_s_4127_, lean_object* v_a_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_IO_eprintln(v_00_u03b1_4125_, v_inst_4126_, v_s_4127_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object* v_s_4130_){
_start:
{
lean_object* v___x_4132_; lean_object* v_putStr_4133_; lean_object* v___x_4134_; 
v___x_4132_ = lean_get_stderr();
v_putStr_4133_ = lean_ctor_get(v___x_4132_, 4);
lean_inc_ref(v_putStr_4133_);
lean_dec_ref(v___x_4132_);
v___x_4134_ = lean_apply_2(v_putStr_4133_, v_s_4130_, lean_box(0));
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0___boxed(lean_object* v_s_4135_, lean_object* v_a_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_4135_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* lean_io_eprint(lean_object* v_s_4138_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_4138_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintAux___boxed(lean_object* v_s_4141_, lean_object* v_a_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = lean_io_eprint(v_s_4141_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object* v_s_4144_){
_start:
{
uint32_t v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4146_ = 10;
v___x_4147_ = lean_string_push(v_s_4144_, v___x_4146_);
v___x_4148_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v___x_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0___boxed(lean_object* v_s_4149_, lean_object* v_a_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_4149_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object* v_s_4152_){
_start:
{
lean_object* v___x_4154_; 
v___x_4154_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_4152_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintlnAux___boxed(lean_object* v_s_4155_, lean_object* v_a_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = lean_io_eprintln(v_s_4155_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_IO_appDir(){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = lean_io_app_path();
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4177_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4164_ = v___x_4161_;
v_isShared_4165_ = v_isSharedCheck_4177_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4161_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4177_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4166_; 
lean_inc(v_a_4162_);
v___x_4166_ = l_System_FilePath_parent(v_a_4162_);
if (lean_obj_tag(v___x_4166_) == 1)
{
lean_object* v_val_4167_; lean_object* v___x_4168_; 
lean_del_object(v___x_4164_);
lean_dec(v_a_4162_);
v_val_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_val_4167_);
lean_dec_ref_known(v___x_4166_, 1);
v___x_4168_ = lean_io_realpath(v_val_4167_);
return v___x_4168_;
}
else
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
lean_dec(v___x_4166_);
v___x_4169_ = ((lean_object*)(l_IO_appDir___closed__0));
v___x_4170_ = lean_string_append(v___x_4169_, v_a_4162_);
lean_dec(v_a_4162_);
v___x_4171_ = ((lean_object*)(l_IO_appDir___closed__1));
v___x_4172_ = lean_string_append(v___x_4170_, v___x_4171_);
v___x_4173_ = lean_mk_io_user_error(v___x_4172_);
if (v_isShared_4165_ == 0)
{
lean_ctor_set_tag(v___x_4164_, 1);
lean_ctor_set(v___x_4164_, 0, v___x_4173_);
v___x_4175_ = v___x_4164_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
else
{
return v___x_4161_;
}
}
}
LEAN_EXPORT lean_object* l_IO_appDir___boxed(lean_object* v_a_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_IO_appDir();
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object* v_p_4180_){
_start:
{
uint8_t v___x_4197_; 
v___x_4197_ = l_System_FilePath_isDir(v_p_4180_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4198_; 
lean_inc_ref(v_p_4180_);
v___x_4198_ = l_System_FilePath_parent(v_p_4180_);
if (lean_obj_tag(v___x_4198_) == 1)
{
lean_object* v_val_4199_; lean_object* v___x_4200_; 
v_val_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_val_4199_);
lean_dec_ref_known(v___x_4198_, 1);
v___x_4200_ = l_IO_FS_createDirAll(v_val_4199_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_dec_ref_known(v___x_4200_, 1);
goto v___jp_4182_;
}
else
{
lean_dec_ref(v_p_4180_);
return v___x_4200_;
}
}
else
{
lean_dec(v___x_4198_);
goto v___jp_4182_;
}
}
else
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
lean_dec_ref(v_p_4180_);
v___x_4201_ = lean_box(0);
v___x_4202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
return v___x_4202_;
}
v___jp_4182_:
{
lean_object* v___x_4183_; 
v___x_4183_ = lean_io_create_dir(v_p_4180_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_dec_ref(v_p_4180_);
return v___x_4183_;
}
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4196_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4186_ = v___x_4183_;
v_isShared_4187_ = v_isSharedCheck_4196_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4183_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4196_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
uint8_t v___x_4188_; 
v___x_4188_ = l_System_FilePath_isDir(v_p_4180_);
lean_dec_ref(v_p_4180_);
if (v___x_4188_ == 0)
{
lean_object* v___x_4190_; 
if (v_isShared_4187_ == 0)
{
v___x_4190_ = v___x_4186_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4184_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
else
{
lean_object* v___x_4192_; lean_object* v___x_4194_; 
lean_dec(v_a_4184_);
v___x_4192_ = lean_box(0);
if (v_isShared_4187_ == 0)
{
lean_ctor_set_tag(v___x_4186_, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4192_);
v___x_4194_ = v___x_4186_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4192_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object* v_p_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_IO_FS_createDirAll(v_p_4203_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(lean_object* v_as_4206_, size_t v_sz_4207_, size_t v_i_4208_, lean_object* v_b_4209_){
_start:
{
lean_object* v_a_4212_; uint8_t v___x_4216_; 
v___x_4216_ = lean_usize_dec_lt(v_i_4208_, v_sz_4207_);
if (v___x_4216_ == 0)
{
lean_object* v___x_4217_; 
v___x_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4217_, 0, v_b_4209_);
return v___x_4217_;
}
else
{
lean_object* v___x_4218_; lean_object* v_a_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4218_ = lean_box(0);
v_a_4219_ = lean_array_uget_borrowed(v_as_4206_, v_i_4208_);
lean_inc(v_a_4219_);
v___x_4220_ = l_IO_FS_DirEntry_path(v_a_4219_);
v___x_4221_ = lean_io_symlink_metadata(v___x_4220_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; uint8_t v_type_4223_; uint8_t v___x_4224_; uint8_t v___x_4225_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_a_4222_);
lean_dec_ref_known(v___x_4221_, 1);
v_type_4223_ = lean_ctor_get_uint8(v_a_4222_, sizeof(void*)*2 + 16);
lean_dec(v_a_4222_);
v___x_4224_ = 0;
v___x_4225_ = l_IO_FS_instBEqFileType_beq(v_type_4223_, v___x_4224_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4226_; 
v___x_4226_ = lean_io_remove_file(v___x_4220_);
lean_dec_ref(v___x_4220_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_dec_ref_known(v___x_4226_, 1);
v_a_4212_ = v___x_4218_;
goto v___jp_4211_;
}
else
{
return v___x_4226_;
}
}
else
{
lean_object* v___x_4227_; 
v___x_4227_ = l_IO_FS_removeDirAll(v___x_4220_);
lean_dec_ref(v___x_4220_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_dec_ref_known(v___x_4227_, 1);
v_a_4212_ = v___x_4218_;
goto v___jp_4211_;
}
else
{
return v___x_4227_;
}
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
lean_dec_ref(v___x_4220_);
v_a_4228_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4221_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4221_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
v___jp_4211_:
{
size_t v___x_4213_; size_t v___x_4214_; 
v___x_4213_ = ((size_t)1ULL);
v___x_4214_ = lean_usize_add(v_i_4208_, v___x_4213_);
v_i_4208_ = v___x_4214_;
v_b_4209_ = v_a_4212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object* v_p_4236_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = lean_io_read_dir(v_p_4236_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v_a_4239_; lean_object* v___x_4240_; size_t v_sz_4241_; size_t v___x_4242_; lean_object* v___x_4243_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
lean_inc(v_a_4239_);
lean_dec_ref_known(v___x_4238_, 1);
v___x_4240_ = lean_box(0);
v_sz_4241_ = lean_array_size(v_a_4239_);
v___x_4242_ = ((size_t)0ULL);
v___x_4243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_a_4239_, v_sz_4241_, v___x_4242_, v___x_4240_);
lean_dec(v_a_4239_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v___x_4244_; 
lean_dec_ref_known(v___x_4243_, 1);
v___x_4244_ = lean_io_remove_dir(v_p_4236_);
return v___x_4244_;
}
else
{
return v___x_4243_;
}
}
else
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
v_a_4245_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4238_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4238_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object* v_p_4253_, lean_object* v_a_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_IO_FS_removeDirAll(v_p_4253_);
lean_dec_ref(v_p_4253_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0___boxed(lean_object* v_as_4256_, lean_object* v_sz_4257_, lean_object* v_i_4258_, lean_object* v_b_4259_, lean_object* v___y_4260_){
_start:
{
size_t v_sz_boxed_4261_; size_t v_i_boxed_4262_; lean_object* v_res_4263_; 
v_sz_boxed_4261_ = lean_unbox_usize(v_sz_4257_);
lean_dec(v_sz_4257_);
v_i_boxed_4262_ = lean_unbox_usize(v_i_4258_);
lean_dec(v_i_4258_);
v_res_4263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_as_4256_, v_sz_boxed_4261_, v_i_boxed_4262_, v_b_4259_);
lean_dec_ref(v_as_4256_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg___lam__2(lean_object* v_toFunctor_4264_, lean_object* v_f_4265_, lean_object* v_inst_4266_, lean_object* v_inst_4267_, lean_object* v___f_4268_, lean_object* v_____x_4269_){
_start:
{
lean_object* v_fst_4270_; lean_object* v_snd_4271_; lean_object* v_map_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___f_4276_; lean_object* v_y_4277_; lean_object* v___x_4278_; 
v_fst_4270_ = lean_ctor_get(v_____x_4269_, 0);
lean_inc(v_fst_4270_);
v_snd_4271_ = lean_ctor_get(v_____x_4269_, 1);
lean_inc_n(v_snd_4271_, 2);
lean_dec_ref(v_____x_4269_);
v_map_4272_ = lean_ctor_get(v_toFunctor_4264_, 0);
lean_inc(v_map_4272_);
lean_dec_ref(v_toFunctor_4264_);
v___x_4273_ = lean_apply_2(v_f_4265_, v_fst_4270_, v_snd_4271_);
v___x_4274_ = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(v___x_4274_, 0, v_snd_4271_);
v___x_4275_ = lean_apply_2(v_inst_4266_, lean_box(0), v___x_4274_);
v___f_4276_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4276_, 0, v___x_4275_);
v_y_4277_ = lean_apply_4(v_inst_4267_, lean_box(0), lean_box(0), v___x_4273_, v___f_4276_);
v___x_4278_ = lean_apply_4(v_map_4272_, lean_box(0), lean_box(0), v___f_4268_, v_y_4277_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg(lean_object* v_inst_4280_, lean_object* v_inst_4281_, lean_object* v_inst_4282_, lean_object* v_f_4283_){
_start:
{
lean_object* v_toApplicative_4284_; lean_object* v_toBind_4285_; lean_object* v_toFunctor_4286_; lean_object* v___f_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___f_4290_; lean_object* v___x_4291_; 
v_toApplicative_4284_ = lean_ctor_get(v_inst_4280_, 0);
lean_inc_ref(v_toApplicative_4284_);
v_toBind_4285_ = lean_ctor_get(v_inst_4280_, 1);
lean_inc(v_toBind_4285_);
lean_dec_ref(v_inst_4280_);
v_toFunctor_4286_ = lean_ctor_get(v_toApplicative_4284_, 0);
lean_inc_ref(v_toFunctor_4286_);
lean_dec_ref(v_toApplicative_4284_);
v___f_4287_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4288_ = ((lean_object*)(l_IO_FS_withTempFile___redArg___closed__0));
lean_inc(v_inst_4282_);
v___x_4289_ = lean_apply_2(v_inst_4282_, lean_box(0), v___x_4288_);
v___f_4290_ = lean_alloc_closure((void*)(l_IO_FS_withTempFile___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4290_, 0, v_toFunctor_4286_);
lean_closure_set(v___f_4290_, 1, v_f_4283_);
lean_closure_set(v___f_4290_, 2, v_inst_4282_);
lean_closure_set(v___f_4290_, 3, v_inst_4281_);
lean_closure_set(v___f_4290_, 4, v___f_4287_);
v___x_4291_ = lean_apply_4(v_toBind_4285_, lean_box(0), lean_box(0), v___x_4289_, v___f_4290_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile(lean_object* v_m_4292_, lean_object* v_00_u03b1_4293_, lean_object* v_inst_4294_, lean_object* v_inst_4295_, lean_object* v_inst_4296_, lean_object* v_f_4297_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_IO_FS_withTempFile___redArg(v_inst_4294_, v_inst_4295_, v_inst_4296_, v_f_4297_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg___lam__2(lean_object* v_toFunctor_4299_, lean_object* v_f_4300_, lean_object* v_inst_4301_, lean_object* v_inst_4302_, lean_object* v___f_4303_, lean_object* v_path_4304_){
_start:
{
lean_object* v_map_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___f_4309_; lean_object* v_y_4310_; lean_object* v___x_4311_; 
v_map_4305_ = lean_ctor_get(v_toFunctor_4299_, 0);
lean_inc(v_map_4305_);
lean_dec_ref(v_toFunctor_4299_);
lean_inc_ref(v_path_4304_);
v___x_4306_ = lean_apply_1(v_f_4300_, v_path_4304_);
v___x_4307_ = lean_alloc_closure((void*)(l_IO_FS_removeDirAll___boxed), 2, 1);
lean_closure_set(v___x_4307_, 0, v_path_4304_);
v___x_4308_ = lean_apply_2(v_inst_4301_, lean_box(0), v___x_4307_);
v___f_4309_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4309_, 0, v___x_4308_);
v_y_4310_ = lean_apply_4(v_inst_4302_, lean_box(0), lean_box(0), v___x_4306_, v___f_4309_);
v___x_4311_ = lean_apply_4(v_map_4305_, lean_box(0), lean_box(0), v___f_4303_, v_y_4310_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg(lean_object* v_inst_4313_, lean_object* v_inst_4314_, lean_object* v_inst_4315_, lean_object* v_f_4316_){
_start:
{
lean_object* v_toApplicative_4317_; lean_object* v_toBind_4318_; lean_object* v_toFunctor_4319_; lean_object* v___f_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___f_4323_; lean_object* v___x_4324_; 
v_toApplicative_4317_ = lean_ctor_get(v_inst_4313_, 0);
lean_inc_ref(v_toApplicative_4317_);
v_toBind_4318_ = lean_ctor_get(v_inst_4313_, 1);
lean_inc(v_toBind_4318_);
lean_dec_ref(v_inst_4313_);
v_toFunctor_4319_ = lean_ctor_get(v_toApplicative_4317_, 0);
lean_inc_ref(v_toFunctor_4319_);
lean_dec_ref(v_toApplicative_4317_);
v___f_4320_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4321_ = ((lean_object*)(l_IO_FS_withTempDir___redArg___closed__0));
lean_inc(v_inst_4315_);
v___x_4322_ = lean_apply_2(v_inst_4315_, lean_box(0), v___x_4321_);
v___f_4323_ = lean_alloc_closure((void*)(l_IO_FS_withTempDir___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4323_, 0, v_toFunctor_4319_);
lean_closure_set(v___f_4323_, 1, v_f_4316_);
lean_closure_set(v___f_4323_, 2, v_inst_4315_);
lean_closure_set(v___f_4323_, 3, v_inst_4314_);
lean_closure_set(v___f_4323_, 4, v___f_4320_);
v___x_4324_ = lean_apply_4(v_toBind_4318_, lean_box(0), lean_box(0), v___x_4322_, v___f_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir(lean_object* v_m_4325_, lean_object* v_00_u03b1_4326_, lean_object* v_inst_4327_, lean_object* v_inst_4328_, lean_object* v_inst_4329_, lean_object* v_f_4330_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_IO_FS_withTempDir___redArg(v_inst_4327_, v_inst_4328_, v_inst_4329_, v_f_4330_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_getCurrentDir___boxed(lean_object* v_a_00___x40___internal___hyg_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = lean_io_process_get_current_dir();
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_setCurrentDir___boxed(lean_object* v_path_4337_, lean_object* v_a_00___x40___internal___hyg_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = lean_io_process_set_current_dir(v_path_4337_);
lean_dec_ref(v_path_4337_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_getPID___boxed(lean_object* v_a_00___x40___internal___hyg_4341_){
_start:
{
uint32_t v_res_4342_; lean_object* v_r_4343_; 
v_res_4342_ = lean_io_process_get_pid();
v_r_4343_ = lean_box_uint32(v_res_4342_);
return v_r_4343_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx___impl(uint8_t v_x_4344_){
_start:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4345_ = lean_box(v_x_4344_);
v___x_4346_ = lean_obj_tag_nat(v___x_4345_);
lean_dec(v___x_4345_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx___impl___boxed(lean_object* v_x_4347_){
_start:
{
uint8_t v_x_4__boxed_4348_; lean_object* v_res_4349_; 
v_x_4__boxed_4348_ = lean_unbox(v_x_4347_);
v_res_4349_ = l_IO_Process_Stdio_ctorIdx___impl(v_x_4__boxed_4348_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg(lean_object* v_k_4350_){
_start:
{
lean_inc(v_k_4350_);
return v_k_4350_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg___boxed(lean_object* v_k_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_IO_Process_Stdio_ctorElim___redArg(v_k_4351_);
lean_dec(v_k_4351_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim(lean_object* v_motive_4353_, lean_object* v_ctorIdx_4354_, uint8_t v_t_4355_, lean_object* v_h_4356_, lean_object* v_k_4357_){
_start:
{
lean_inc(v_k_4357_);
return v_k_4357_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___boxed(lean_object* v_motive_4358_, lean_object* v_ctorIdx_4359_, lean_object* v_t_4360_, lean_object* v_h_4361_, lean_object* v_k_4362_){
_start:
{
uint8_t v_t_boxed_4363_; lean_object* v_res_4364_; 
v_t_boxed_4363_ = lean_unbox(v_t_4360_);
v_res_4364_ = l_IO_Process_Stdio_ctorElim(v_motive_4358_, v_ctorIdx_4359_, v_t_boxed_4363_, v_h_4361_, v_k_4362_);
lean_dec(v_k_4362_);
lean_dec(v_ctorIdx_4359_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg(lean_object* v_piped_4365_){
_start:
{
lean_inc(v_piped_4365_);
return v_piped_4365_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg___boxed(lean_object* v_piped_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_IO_Process_Stdio_piped_elim___redArg(v_piped_4366_);
lean_dec(v_piped_4366_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim(lean_object* v_motive_4368_, uint8_t v_t_4369_, lean_object* v_h_4370_, lean_object* v_piped_4371_){
_start:
{
lean_inc(v_piped_4371_);
return v_piped_4371_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___boxed(lean_object* v_motive_4372_, lean_object* v_t_4373_, lean_object* v_h_4374_, lean_object* v_piped_4375_){
_start:
{
uint8_t v_t_boxed_4376_; lean_object* v_res_4377_; 
v_t_boxed_4376_ = lean_unbox(v_t_4373_);
v_res_4377_ = l_IO_Process_Stdio_piped_elim(v_motive_4372_, v_t_boxed_4376_, v_h_4374_, v_piped_4375_);
lean_dec(v_piped_4375_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg(lean_object* v_inherit_4378_){
_start:
{
lean_inc(v_inherit_4378_);
return v_inherit_4378_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg___boxed(lean_object* v_inherit_4379_){
_start:
{
lean_object* v_res_4380_; 
v_res_4380_ = l_IO_Process_Stdio_inherit_elim___redArg(v_inherit_4379_);
lean_dec(v_inherit_4379_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim(lean_object* v_motive_4381_, uint8_t v_t_4382_, lean_object* v_h_4383_, lean_object* v_inherit_4384_){
_start:
{
lean_inc(v_inherit_4384_);
return v_inherit_4384_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___boxed(lean_object* v_motive_4385_, lean_object* v_t_4386_, lean_object* v_h_4387_, lean_object* v_inherit_4388_){
_start:
{
uint8_t v_t_boxed_4389_; lean_object* v_res_4390_; 
v_t_boxed_4389_ = lean_unbox(v_t_4386_);
v_res_4390_ = l_IO_Process_Stdio_inherit_elim(v_motive_4385_, v_t_boxed_4389_, v_h_4387_, v_inherit_4388_);
lean_dec(v_inherit_4388_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg(lean_object* v_null_4391_){
_start:
{
lean_inc(v_null_4391_);
return v_null_4391_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg___boxed(lean_object* v_null_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_IO_Process_Stdio_null_elim___redArg(v_null_4392_);
lean_dec(v_null_4392_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim(lean_object* v_motive_4394_, uint8_t v_t_4395_, lean_object* v_h_4396_, lean_object* v_null_4397_){
_start:
{
lean_inc(v_null_4397_);
return v_null_4397_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___boxed(lean_object* v_motive_4398_, lean_object* v_t_4399_, lean_object* v_h_4400_, lean_object* v_null_4401_){
_start:
{
uint8_t v_t_boxed_4402_; lean_object* v_res_4403_; 
v_t_boxed_4402_ = lean_unbox(v_t_4399_);
v_res_4403_ = l_IO_Process_Stdio_null_elim(v_motive_4398_, v_t_boxed_4402_, v_h_4400_, v_null_4401_);
lean_dec(v_null_4401_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object* v_args_4406_, lean_object* v_a_00___x40___internal___hyg_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = lean_io_process_spawn(v_args_4406_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object* v_cfg_4412_, lean_object* v_a_00___x40___internal___hyg_4413_, lean_object* v_a_00___x40___internal___hyg_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = lean_io_process_child_wait(v_cfg_4412_, v_a_00___x40___internal___hyg_4413_);
lean_dec_ref(v_a_00___x40___internal___hyg_4413_);
lean_dec_ref(v_cfg_4412_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_tryWait___boxed(lean_object* v_cfg_4419_, lean_object* v_a_00___x40___internal___hyg_4420_, lean_object* v_a_00___x40___internal___hyg_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = lean_io_process_child_try_wait(v_cfg_4419_, v_a_00___x40___internal___hyg_4420_);
lean_dec_ref(v_a_00___x40___internal___hyg_4420_);
lean_dec_ref(v_cfg_4419_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_kill___boxed(lean_object* v_cfg_4426_, lean_object* v_a_00___x40___internal___hyg_4427_, lean_object* v_a_00___x40___internal___hyg_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = lean_io_process_child_kill(v_cfg_4426_, v_a_00___x40___internal___hyg_4427_);
lean_dec_ref(v_a_00___x40___internal___hyg_4427_);
lean_dec_ref(v_cfg_4426_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object* v_cfg_4433_, lean_object* v_a_00___x40___internal___hyg_4434_, lean_object* v_a_00___x40___internal___hyg_4435_){
_start:
{
lean_object* v_res_4436_; 
v_res_4436_ = lean_io_process_child_take_stdin(v_cfg_4433_, v_a_00___x40___internal___hyg_4434_);
lean_dec_ref(v_cfg_4433_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_pid___boxed(lean_object* v_cfg_4439_, lean_object* v_a_00___x40___internal___hyg_4440_){
_start:
{
uint32_t v_res_4441_; lean_object* v_r_4442_; 
v_res_4441_ = lean_io_process_child_pid(v_cfg_4439_, v_a_00___x40___internal___hyg_4440_);
lean_dec_ref(v_a_00___x40___internal___hyg_4440_);
lean_dec_ref(v_cfg_4439_);
v_r_4442_ = lean_box_uint32(v_res_4441_);
return v_r_4442_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(lean_object* v_e_4443_){
_start:
{
if (lean_obj_tag(v_e_4443_) == 0)
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4454_; 
v_a_4445_ = lean_ctor_get(v_e_4443_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v_e_4443_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4447_ = v_e_4443_;
v_isShared_4448_ = v_isSharedCheck_4454_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v_e_4443_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4454_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4452_; 
v___x_4449_ = lean_io_error_to_string(v_a_4445_);
v___x_4450_ = lean_mk_io_user_error(v___x_4449_);
if (v_isShared_4448_ == 0)
{
lean_ctor_set_tag(v___x_4447_, 1);
lean_ctor_set(v___x_4447_, 0, v___x_4450_);
v___x_4452_ = v___x_4447_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4450_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
v_a_4455_ = lean_ctor_get(v_e_4443_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_e_4443_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v_e_4443_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v_e_4443_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
lean_ctor_set_tag(v___x_4457_, 0);
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg___boxed(lean_object* v_e_4463_, lean_object* v_a_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_4463_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0(lean_object* v_00_u03b1_4466_, lean_object* v_e_4467_){
_start:
{
lean_object* v___x_4469_; 
v___x_4469_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_4467_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___boxed(lean_object* v_00_u03b1_4470_, lean_object* v_e_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_IO_ofExcept___at___00IO_Process_output_spec__0(v_00_u03b1_4470_, v_e_4471_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0(lean_object* v_stdout_4474_){
_start:
{
lean_object* v___x_4476_; 
v___x_4476_ = l_IO_FS_Handle_readToEnd(v_stdout_4474_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4479_ = v___x_4476_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4476_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
lean_ctor_set_tag(v___x_4479_, 1);
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
else
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
v_a_4485_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v___x_4476_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4476_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
lean_ctor_set_tag(v___x_4487_, 0);
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0___boxed(lean_object* v_stdout_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l_IO_Process_output___lam__0(v_stdout_4493_);
lean_dec(v_stdout_4493_);
return v_res_4495_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object* v_args_4501_, lean_object* v_input_x3f_4502_){
_start:
{
lean_object* v_child_4505_; 
if (lean_obj_tag(v_input_x3f_4502_) == 1)
{
lean_object* v_val_4552_; lean_object* v___x_4553_; lean_object* v_cmd_4554_; lean_object* v_args_4555_; lean_object* v_cwd_4556_; lean_object* v_env_4557_; uint8_t v_inheritEnv_4558_; uint8_t v_setsid_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4606_; 
v_val_4552_ = lean_ctor_get(v_input_x3f_4502_, 0);
v___x_4553_ = ((lean_object*)(l_IO_Process_output___closed__1));
v_cmd_4554_ = lean_ctor_get(v_args_4501_, 1);
v_args_4555_ = lean_ctor_get(v_args_4501_, 2);
v_cwd_4556_ = lean_ctor_get(v_args_4501_, 3);
v_env_4557_ = lean_ctor_get(v_args_4501_, 4);
v_inheritEnv_4558_ = lean_ctor_get_uint8(v_args_4501_, sizeof(void*)*5);
v_setsid_4559_ = lean_ctor_get_uint8(v_args_4501_, sizeof(void*)*5 + 1);
v_isSharedCheck_4606_ = !lean_is_exclusive(v_args_4501_);
if (v_isSharedCheck_4606_ == 0)
{
lean_object* v_unused_4607_; 
v_unused_4607_ = lean_ctor_get(v_args_4501_, 0);
lean_dec(v_unused_4607_);
v___x_4561_ = v_args_4501_;
v_isShared_4562_ = v_isSharedCheck_4606_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_env_4557_);
lean_inc(v_cwd_4556_);
lean_inc(v_args_4555_);
lean_inc(v_cmd_4554_);
lean_dec(v_args_4501_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4606_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 0, v___x_4553_);
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4553_);
lean_ctor_set(v_reuseFailAlloc_4605_, 1, v_cmd_4554_);
lean_ctor_set(v_reuseFailAlloc_4605_, 2, v_args_4555_);
lean_ctor_set(v_reuseFailAlloc_4605_, 3, v_cwd_4556_);
lean_ctor_set(v_reuseFailAlloc_4605_, 4, v_env_4557_);
lean_ctor_set_uint8(v_reuseFailAlloc_4605_, sizeof(void*)*5, v_inheritEnv_4558_);
lean_ctor_set_uint8(v_reuseFailAlloc_4605_, sizeof(void*)*5 + 1, v_setsid_4559_);
v___x_4564_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
lean_object* v___x_4565_; 
v___x_4565_ = lean_io_process_spawn(v___x_4564_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v___x_4567_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v___x_4565_, 1);
v___x_4567_ = lean_io_process_child_take_stdin(v___x_4553_, v_a_4566_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_object* v_a_4568_; lean_object* v_fst_4569_; lean_object* v_snd_4570_; lean_object* v___x_4571_; 
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
lean_inc(v_a_4568_);
lean_dec_ref_known(v___x_4567_, 1);
v_fst_4569_ = lean_ctor_get(v_a_4568_, 0);
lean_inc(v_fst_4569_);
v_snd_4570_ = lean_ctor_get(v_a_4568_, 1);
lean_inc(v_snd_4570_);
lean_dec(v_a_4568_);
v___x_4571_ = lean_io_prim_handle_put_str(v_fst_4569_, v_val_4552_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v___x_4572_; 
lean_dec_ref_known(v___x_4571_, 1);
v___x_4572_ = lean_io_prim_handle_flush(v_fst_4569_);
lean_dec(v_fst_4569_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_dec_ref_known(v___x_4572_, 1);
v_child_4505_ = v_snd_4570_;
goto v___jp_4504_;
}
else
{
lean_object* v_a_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4580_; 
lean_dec(v_snd_4570_);
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4575_ = v___x_4572_;
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_a_4573_);
lean_dec(v___x_4572_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4578_; 
if (v_isShared_4576_ == 0)
{
v___x_4578_ = v___x_4575_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4573_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
}
}
else
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4588_; 
lean_dec(v_snd_4570_);
lean_dec(v_fst_4569_);
v_a_4581_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4588_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4583_ = v___x_4571_;
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v___x_4571_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4586_; 
if (v_isShared_4584_ == 0)
{
v___x_4586_ = v___x_4583_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_a_4581_);
v___x_4586_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
return v___x_4586_;
}
}
}
}
else
{
lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4596_; 
v_a_4589_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4591_ = v___x_4567_;
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___x_4567_);
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
else
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4604_; 
v_a_4597_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4599_ = v___x_4565_;
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4565_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4602_; 
if (v_isShared_4600_ == 0)
{
v___x_4602_ = v___x_4599_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4597_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
}
}
}
else
{
lean_object* v___x_4608_; lean_object* v_cmd_4609_; lean_object* v_args_4610_; lean_object* v_cwd_4611_; lean_object* v_env_4612_; uint8_t v_inheritEnv_4613_; uint8_t v_setsid_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4631_; 
v___x_4608_ = ((lean_object*)(l_IO_Process_output___closed__0));
v_cmd_4609_ = lean_ctor_get(v_args_4501_, 1);
v_args_4610_ = lean_ctor_get(v_args_4501_, 2);
v_cwd_4611_ = lean_ctor_get(v_args_4501_, 3);
v_env_4612_ = lean_ctor_get(v_args_4501_, 4);
v_inheritEnv_4613_ = lean_ctor_get_uint8(v_args_4501_, sizeof(void*)*5);
v_setsid_4614_ = lean_ctor_get_uint8(v_args_4501_, sizeof(void*)*5 + 1);
v_isSharedCheck_4631_ = !lean_is_exclusive(v_args_4501_);
if (v_isSharedCheck_4631_ == 0)
{
lean_object* v_unused_4632_; 
v_unused_4632_ = lean_ctor_get(v_args_4501_, 0);
lean_dec(v_unused_4632_);
v___x_4616_ = v_args_4501_;
v_isShared_4617_ = v_isSharedCheck_4631_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_env_4612_);
lean_inc(v_cwd_4611_);
lean_inc(v_args_4610_);
lean_inc(v_cmd_4609_);
lean_dec(v_args_4501_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4631_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v___x_4608_);
v___x_4619_ = v___x_4616_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4608_);
lean_ctor_set(v_reuseFailAlloc_4630_, 1, v_cmd_4609_);
lean_ctor_set(v_reuseFailAlloc_4630_, 2, v_args_4610_);
lean_ctor_set(v_reuseFailAlloc_4630_, 3, v_cwd_4611_);
lean_ctor_set(v_reuseFailAlloc_4630_, 4, v_env_4612_);
lean_ctor_set_uint8(v_reuseFailAlloc_4630_, sizeof(void*)*5, v_inheritEnv_4613_);
lean_ctor_set_uint8(v_reuseFailAlloc_4630_, sizeof(void*)*5 + 1, v_setsid_4614_);
v___x_4619_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
lean_object* v___x_4620_; 
v___x_4620_ = lean_io_process_spawn(v___x_4619_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
lean_inc(v_a_4621_);
lean_dec_ref_known(v___x_4620_, 1);
v_child_4505_ = v_a_4621_;
goto v___jp_4504_;
}
else
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4629_; 
v_a_4622_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4624_ = v___x_4620_;
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4620_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4627_; 
if (v_isShared_4625_ == 0)
{
v___x_4627_ = v___x_4624_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_a_4622_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
}
}
}
v___jp_4504_:
{
lean_object* v_stdout_4506_; lean_object* v_stderr_4507_; lean_object* v___f_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v_stdout_4506_ = lean_ctor_get(v_child_4505_, 1);
v_stderr_4507_ = lean_ctor_get(v_child_4505_, 2);
lean_inc(v_stdout_4506_);
v___f_4508_ = lean_alloc_closure((void*)(l_IO_Process_output___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4508_, 0, v_stdout_4506_);
v___x_4509_ = lean_unsigned_to_nat(9u);
v___x_4510_ = lean_io_as_task(v___f_4508_, v___x_4509_);
v___x_4511_ = l_IO_FS_Handle_readToEnd(v_stderr_4507_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4512_);
lean_dec_ref_known(v___x_4511_, 1);
v___x_4513_ = ((lean_object*)(l_IO_Process_output___closed__0));
v___x_4514_ = lean_io_process_child_wait(v___x_4513_, v_child_4505_);
lean_dec_ref(v_child_4505_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_object* v_a_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
lean_inc(v_a_4515_);
lean_dec_ref_known(v___x_4514_, 1);
v___x_4516_ = lean_task_get_own(v___x_4510_);
v___x_4517_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v___x_4516_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4527_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4520_ = v___x_4517_;
v_isShared_4521_ = v_isSharedCheck_4527_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4517_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4527_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4522_; uint32_t v___x_4523_; lean_object* v___x_4525_; 
v___x_4522_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4522_, 0, v_a_4518_);
lean_ctor_set(v___x_4522_, 1, v_a_4512_);
v___x_4523_ = lean_unbox_uint32(v_a_4515_);
lean_dec(v_a_4515_);
lean_ctor_set_uint32(v___x_4522_, sizeof(void*)*2, v___x_4523_);
if (v_isShared_4521_ == 0)
{
lean_ctor_set(v___x_4520_, 0, v___x_4522_);
v___x_4525_ = v___x_4520_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4522_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
else
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4535_; 
lean_dec(v_a_4515_);
lean_dec(v_a_4512_);
v_a_4528_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4530_ = v___x_4517_;
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4517_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4533_; 
if (v_isShared_4531_ == 0)
{
v___x_4533_ = v___x_4530_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_a_4528_);
v___x_4533_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
return v___x_4533_;
}
}
}
}
else
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
lean_dec(v_a_4512_);
lean_dec_ref(v___x_4510_);
v_a_4536_ = lean_ctor_get(v___x_4514_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4514_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4514_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
lean_dec_ref(v___x_4510_);
lean_dec_ref(v_child_4505_);
v_a_4544_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4511_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4511_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___boxed(lean_object* v_args_4633_, lean_object* v_input_x3f_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_IO_Process_output(v_args_4633_, v_input_x3f_4634_);
lean_dec(v_input_x3f_4634_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_run(lean_object* v_args_4640_, lean_object* v_input_x3f_4641_){
_start:
{
lean_object* v___x_4643_; 
lean_inc_ref(v_args_4640_);
v___x_4643_ = l_IO_Process_output(v_args_4640_, v_input_x3f_4641_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4671_; 
v_a_4644_ = lean_ctor_get(v___x_4643_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4646_ = v___x_4643_;
v_isShared_4647_ = v_isSharedCheck_4671_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4643_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4671_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
uint32_t v_exitCode_4648_; lean_object* v_stdout_4649_; lean_object* v_stderr_4650_; uint32_t v___x_4651_; uint8_t v___x_4652_; 
v_exitCode_4648_ = lean_ctor_get_uint32(v_a_4644_, sizeof(void*)*2);
v_stdout_4649_ = lean_ctor_get(v_a_4644_, 0);
lean_inc_ref(v_stdout_4649_);
v_stderr_4650_ = lean_ctor_get(v_a_4644_, 1);
lean_inc_ref(v_stderr_4650_);
lean_dec(v_a_4644_);
v___x_4651_ = 0;
v___x_4652_ = lean_uint32_dec_eq(v_exitCode_4648_, v___x_4651_);
if (v___x_4652_ == 0)
{
lean_object* v_cmd_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4666_; 
lean_dec_ref(v_stdout_4649_);
v_cmd_4653_ = lean_ctor_get(v_args_4640_, 1);
lean_inc_ref(v_cmd_4653_);
lean_dec_ref(v_args_4640_);
v___x_4654_ = ((lean_object*)(l_IO_Process_run___closed__0));
v___x_4655_ = lean_string_append(v___x_4654_, v_cmd_4653_);
lean_dec_ref(v_cmd_4653_);
v___x_4656_ = ((lean_object*)(l_IO_Process_run___closed__1));
v___x_4657_ = lean_string_append(v___x_4655_, v___x_4656_);
v___x_4658_ = lean_uint32_to_nat(v_exitCode_4648_);
v___x_4659_ = l_Nat_reprFast(v___x_4658_);
v___x_4660_ = lean_string_append(v___x_4657_, v___x_4659_);
lean_dec_ref(v___x_4659_);
v___x_4661_ = ((lean_object*)(l_IO_Process_run___closed__2));
v___x_4662_ = lean_string_append(v___x_4660_, v___x_4661_);
v___x_4663_ = lean_string_append(v___x_4662_, v_stderr_4650_);
lean_dec_ref(v_stderr_4650_);
v___x_4664_ = lean_mk_io_user_error(v___x_4663_);
if (v_isShared_4647_ == 0)
{
lean_ctor_set_tag(v___x_4646_, 1);
lean_ctor_set(v___x_4646_, 0, v___x_4664_);
v___x_4666_ = v___x_4646_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v___x_4664_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
return v___x_4666_;
}
}
else
{
lean_object* v___x_4669_; 
lean_dec_ref(v_stderr_4650_);
lean_dec_ref(v_args_4640_);
if (v_isShared_4647_ == 0)
{
lean_ctor_set(v___x_4646_, 0, v_stdout_4649_);
v___x_4669_ = v___x_4646_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_stdout_4649_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
lean_dec_ref(v_args_4640_);
v_a_4672_ = lean_ctor_get(v___x_4643_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4643_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4643_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4643_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_run___boxed(lean_object* v_args_4680_, lean_object* v_input_x3f_4681_, lean_object* v_a_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l_IO_Process_run(v_args_4680_, v_input_x3f_4681_);
lean_dec(v_input_x3f_4681_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object* v_00_u03b1_4687_, lean_object* v_a_00___x40___internal___hyg_4688_, lean_object* v_a_00___x40___internal___hyg_4689_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_4690_; lean_object* v_res_4691_; 
v_a_00___x40___internal___hyg_1__boxed_4690_ = lean_unbox(v_a_00___x40___internal___hyg_4688_);
v_res_4691_ = lean_io_exit(v_a_00___x40___internal___hyg_1__boxed_4690_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_forceExit___boxed(lean_object* v_00_u03b1_4695_, lean_object* v_a_00___x40___internal___hyg_4696_, lean_object* v_a_00___x40___internal___hyg_4697_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_4698_; lean_object* v_res_4699_; 
v_a_00___x40___internal___hyg_1__boxed_4698_ = lean_unbox(v_a_00___x40___internal___hyg_4696_);
v_res_4699_ = lean_io_force_exit(v_a_00___x40___internal___hyg_1__boxed_4698_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l_IO_getTID___boxed(lean_object* v_a_00___x40___internal___hyg_4701_){
_start:
{
uint64_t v_res_4702_; lean_object* v_r_4703_; 
v_res_4702_ = lean_io_get_tid();
v_r_4703_ = lean_box_uint64(v_res_4702_);
return v_r_4703_;
}
}
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object* v_acc_4704_){
_start:
{
uint32_t v___y_4706_; uint32_t v___y_4707_; uint32_t v___y_4708_; uint8_t v_read_4711_; uint8_t v_write_4712_; uint8_t v_execution_4713_; uint32_t v___y_4715_; uint32_t v___y_4716_; uint32_t v___y_4720_; 
v_read_4711_ = lean_ctor_get_uint8(v_acc_4704_, 0);
v_write_4712_ = lean_ctor_get_uint8(v_acc_4704_, 1);
v_execution_4713_ = lean_ctor_get_uint8(v_acc_4704_, 2);
if (v_read_4711_ == 0)
{
uint32_t v___x_4723_; 
v___x_4723_ = 0;
v___y_4720_ = v___x_4723_;
goto v___jp_4719_;
}
else
{
uint32_t v___x_4724_; 
v___x_4724_ = 4;
v___y_4720_ = v___x_4724_;
goto v___jp_4719_;
}
v___jp_4705_:
{
uint32_t v___x_4709_; uint32_t v___x_4710_; 
v___x_4709_ = lean_uint32_lor(v___y_4707_, v___y_4708_);
v___x_4710_ = lean_uint32_lor(v___y_4706_, v___x_4709_);
return v___x_4710_;
}
v___jp_4714_:
{
if (v_execution_4713_ == 0)
{
uint32_t v___x_4717_; 
v___x_4717_ = 0;
v___y_4706_ = v___y_4715_;
v___y_4707_ = v___y_4716_;
v___y_4708_ = v___x_4717_;
goto v___jp_4705_;
}
else
{
uint32_t v___x_4718_; 
v___x_4718_ = 1;
v___y_4706_ = v___y_4715_;
v___y_4707_ = v___y_4716_;
v___y_4708_ = v___x_4718_;
goto v___jp_4705_;
}
}
v___jp_4719_:
{
if (v_write_4712_ == 0)
{
uint32_t v___x_4721_; 
v___x_4721_ = 0;
v___y_4715_ = v___y_4720_;
v___y_4716_ = v___x_4721_;
goto v___jp_4714_;
}
else
{
uint32_t v___x_4722_; 
v___x_4722_ = 2;
v___y_4715_ = v___y_4720_;
v___y_4716_ = v___x_4722_;
goto v___jp_4714_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object* v_acc_4725_){
_start:
{
uint32_t v_res_4726_; lean_object* v_r_4727_; 
v_res_4726_ = l_IO_AccessRight_flags(v_acc_4725_);
lean_dec_ref(v_acc_4725_);
v_r_4727_ = lean_box_uint32(v_res_4726_);
return v_r_4727_;
}
}
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object* v_acc_4728_){
_start:
{
lean_object* v_user_4729_; lean_object* v_group_4730_; lean_object* v_other_4731_; uint32_t v___x_4732_; uint32_t v___x_4733_; uint32_t v_u_4734_; uint32_t v___x_4735_; uint32_t v___x_4736_; uint32_t v_g_4737_; uint32_t v_o_4738_; uint32_t v___x_4739_; uint32_t v___x_4740_; 
v_user_4729_ = lean_ctor_get(v_acc_4728_, 0);
v_group_4730_ = lean_ctor_get(v_acc_4728_, 1);
v_other_4731_ = lean_ctor_get(v_acc_4728_, 2);
v___x_4732_ = l_IO_AccessRight_flags(v_user_4729_);
v___x_4733_ = 6;
v_u_4734_ = lean_uint32_shift_left(v___x_4732_, v___x_4733_);
v___x_4735_ = l_IO_AccessRight_flags(v_group_4730_);
v___x_4736_ = 3;
v_g_4737_ = lean_uint32_shift_left(v___x_4735_, v___x_4736_);
v_o_4738_ = l_IO_AccessRight_flags(v_other_4731_);
v___x_4739_ = lean_uint32_lor(v_g_4737_, v_o_4738_);
v___x_4740_ = lean_uint32_lor(v_u_4734_, v___x_4739_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object* v_acc_4741_){
_start:
{
uint32_t v_res_4742_; lean_object* v_r_4743_; 
v_res_4742_ = l_IO_FileRight_flags(v_acc_4741_);
lean_dec_ref(v_acc_4741_);
v_r_4743_ = lean_box_uint32(v_res_4742_);
return v_r_4743_;
}
}
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object* v_filename_4747_, lean_object* v_mode_4748_, lean_object* v_a_00___x40___internal___hyg_4749_){
_start:
{
uint32_t v_mode_boxed_4750_; lean_object* v_res_4751_; 
v_mode_boxed_4750_ = lean_unbox_uint32(v_mode_4748_);
lean_dec(v_mode_4748_);
v_res_4751_ = lean_chmod(v_filename_4747_, v_mode_boxed_4750_);
lean_dec_ref(v_filename_4747_);
return v_res_4751_;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object* v_filename_4752_, lean_object* v_mode_4753_){
_start:
{
uint32_t v___x_4755_; lean_object* v___x_4756_; 
v___x_4755_ = l_IO_FileRight_flags(v_mode_4753_);
v___x_4756_ = lean_chmod(v_filename_4752_, v___x_4755_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object* v_filename_4757_, lean_object* v_mode_4758_, lean_object* v_a_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l_IO_setAccessRights(v_filename_4757_, v_mode_4758_);
lean_dec_ref(v_mode_4758_);
lean_dec_ref(v_filename_4757_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object* v_00_u03b1_4761_, lean_object* v_mx_4762_){
_start:
{
lean_object* v___x_4764_; 
v___x_4764_ = lean_apply_1(v_mx_4762_, lean_box(0));
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object* v_00_u03b1_4765_, lean_object* v_mx_4766_, lean_object* v_s_4767_){
_start:
{
lean_object* v_res_4768_; 
v_res_4768_ = l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(v_00_u03b1_4765_, v_mx_4766_);
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg(lean_object* v_a_4771_){
_start:
{
lean_object* v___x_4773_; 
v___x_4773_ = lean_st_mk_ref(v_a_4771_);
return v___x_4773_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg___boxed(lean_object* v_a_4774_, lean_object* v_a_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l_IO_mkRef___redArg(v_a_4774_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object* v_00_u03b1_4777_, lean_object* v_a_4778_){
_start:
{
lean_object* v___x_4780_; 
v___x_4780_ = lean_st_mk_ref(v_a_4778_);
return v___x_4780_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___boxed(lean_object* v_00_u03b1_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_){
_start:
{
lean_object* v_res_4784_; 
v_res_4784_ = l_IO_mkRef(v_00_u03b1_4781_, v_a_4782_);
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object* v_h_4785_){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; 
lean_inc_n(v_h_4785_, 5);
v___x_4786_ = lean_alloc_closure((void*)(l_IO_FS_Handle_flush___boxed), 2, 1);
lean_closure_set(v___x_4786_, 0, v_h_4785_);
v___x_4787_ = lean_alloc_closure((void*)(l_IO_FS_Handle_read___boxed), 3, 1);
lean_closure_set(v___x_4787_, 0, v_h_4785_);
v___x_4788_ = lean_alloc_closure((void*)(l_IO_FS_Handle_write___boxed), 3, 1);
lean_closure_set(v___x_4788_, 0, v_h_4785_);
v___x_4789_ = lean_alloc_closure((void*)(l_IO_FS_Handle_getLine___boxed), 2, 1);
lean_closure_set(v___x_4789_, 0, v_h_4785_);
v___x_4790_ = lean_alloc_closure((void*)(l_IO_FS_Handle_putStr___boxed), 3, 1);
lean_closure_set(v___x_4790_, 0, v_h_4785_);
v___x_4791_ = lean_alloc_closure((void*)(l_IO_FS_Handle_isTty___boxed), 2, 1);
lean_closure_set(v___x_4791_, 0, v_h_4785_);
v___x_4792_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4786_);
lean_ctor_set(v___x_4792_, 1, v___x_4787_);
lean_ctor_set(v___x_4792_, 2, v___x_4788_);
lean_ctor_set(v___x_4792_, 3, v___x_4789_);
lean_ctor_set(v___x_4792_, 4, v___x_4790_);
lean_ctor_set(v___x_4792_, 5, v___x_4791_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0(lean_object* v_r_4793_, size_t v_n_4794_){
_start:
{
lean_object* v___x_4796_; lean_object* v_data_4797_; lean_object* v_pos_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4812_; 
v___x_4796_ = lean_st_ref_take(v_r_4793_);
v_data_4797_ = lean_ctor_get(v___x_4796_, 0);
v_pos_4798_ = lean_ctor_get(v___x_4796_, 1);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4800_ = v___x_4796_;
v_isShared_4801_ = v_isSharedCheck_4812_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_pos_4798_);
lean_inc(v_data_4797_);
lean_dec(v___x_4796_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4812_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v_data_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4808_; 
v___x_4802_ = lean_usize_to_nat(v_n_4794_);
v___x_4803_ = lean_nat_add(v_pos_4798_, v___x_4802_);
lean_dec(v___x_4802_);
lean_inc(v_pos_4798_);
v_data_4804_ = l_ByteArray_extract(v_data_4797_, v_pos_4798_, v___x_4803_);
lean_dec(v___x_4803_);
v___x_4805_ = lean_byte_array_size(v_data_4804_);
v___x_4806_ = lean_nat_add(v_pos_4798_, v___x_4805_);
lean_dec(v_pos_4798_);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 1, v___x_4806_);
v___x_4808_ = v___x_4800_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_data_4797_);
lean_ctor_set(v_reuseFailAlloc_4811_, 1, v___x_4806_);
v___x_4808_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4809_ = lean_st_ref_put(v_r_4793_, v___x_4808_);
v___x_4810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4810_, 0, v_data_4804_);
return v___x_4810_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0___boxed(lean_object* v_r_4813_, lean_object* v_n_4814_, lean_object* v___y_4815_){
_start:
{
size_t v_n_boxed_4816_; lean_object* v_res_4817_; 
v_n_boxed_4816_ = lean_unbox_usize(v_n_4814_);
lean_dec(v_n_4814_);
v_res_4817_ = l_IO_FS_Stream_ofBuffer___lam__0(v_r_4813_, v_n_boxed_4816_);
lean_dec(v_r_4813_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1(lean_object* v_r_4818_, lean_object* v_data_4819_){
_start:
{
lean_object* v___x_4821_; lean_object* v_data_4822_; lean_object* v_pos_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4837_; 
v___x_4821_ = lean_st_ref_take(v_r_4818_);
v_data_4822_ = lean_ctor_get(v___x_4821_, 0);
v_pos_4823_ = lean_ctor_get(v___x_4821_, 1);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4825_ = v___x_4821_;
v_isShared_4826_ = v_isSharedCheck_4837_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_pos_4823_);
lean_inc(v_data_4822_);
lean_dec(v___x_4821_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4837_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; uint8_t v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4833_; 
v___x_4827_ = lean_unsigned_to_nat(0u);
v___x_4828_ = lean_byte_array_size(v_data_4819_);
v___x_4829_ = 0;
lean_inc(v_pos_4823_);
v___x_4830_ = lean_byte_array_copy_slice(v_data_4819_, v___x_4827_, v_data_4822_, v_pos_4823_, v___x_4828_, v___x_4829_);
v___x_4831_ = lean_nat_add(v_pos_4823_, v___x_4828_);
lean_dec(v_pos_4823_);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 1, v___x_4831_);
lean_ctor_set(v___x_4825_, 0, v___x_4830_);
v___x_4833_ = v___x_4825_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v___x_4830_);
lean_ctor_set(v_reuseFailAlloc_4836_, 1, v___x_4831_);
v___x_4833_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4834_ = lean_st_ref_put(v_r_4818_, v___x_4833_);
v___x_4835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4835_, 0, v___x_4834_);
return v___x_4835_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1___boxed(lean_object* v_r_4838_, lean_object* v_data_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l_IO_FS_Stream_ofBuffer___lam__1(v_r_4838_, v_data_4839_);
lean_dec_ref(v_data_4839_);
lean_dec(v_r_4838_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2(lean_object* v_r_4842_, lean_object* v_s_4843_){
_start:
{
lean_object* v___x_4845_; lean_object* v_data_4846_; lean_object* v_pos_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4862_; 
v___x_4845_ = lean_st_ref_take(v_r_4842_);
v_data_4846_ = lean_ctor_get(v___x_4845_, 0);
v_pos_4847_ = lean_ctor_get(v___x_4845_, 1);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4849_ = v___x_4845_;
v_isShared_4850_ = v_isSharedCheck_4862_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_pos_4847_);
lean_inc(v_data_4846_);
lean_dec(v___x_4845_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4862_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v_data_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; uint8_t v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4858_; 
v_data_4851_ = lean_string_to_utf8(v_s_4843_);
v___x_4852_ = lean_unsigned_to_nat(0u);
v___x_4853_ = lean_byte_array_size(v_data_4851_);
v___x_4854_ = 0;
lean_inc(v_pos_4847_);
v___x_4855_ = lean_byte_array_copy_slice(v_data_4851_, v___x_4852_, v_data_4846_, v_pos_4847_, v___x_4853_, v___x_4854_);
lean_dec_ref(v_data_4851_);
v___x_4856_ = lean_nat_add(v_pos_4847_, v___x_4853_);
lean_dec(v_pos_4847_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 1, v___x_4856_);
lean_ctor_set(v___x_4849_, 0, v___x_4855_);
v___x_4858_ = v___x_4849_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4855_);
lean_ctor_set(v_reuseFailAlloc_4861_, 1, v___x_4856_);
v___x_4858_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4859_ = lean_st_ref_put(v_r_4842_, v___x_4858_);
v___x_4860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4859_);
return v___x_4860_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2___boxed(lean_object* v_r_4863_, lean_object* v_s_4864_, lean_object* v___y_4865_){
_start:
{
lean_object* v_res_4866_; 
v_res_4866_ = l_IO_FS_Stream_ofBuffer___lam__2(v_r_4863_, v_s_4864_);
lean_dec(v_r_4863_);
return v_res_4866_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(lean_object* v_a_4867_, lean_object* v_i_4868_){
_start:
{
lean_object* v___x_4869_; uint8_t v___x_4870_; 
v___x_4869_ = lean_byte_array_size(v_a_4867_);
v___x_4870_ = lean_nat_dec_lt(v_i_4868_, v___x_4869_);
if (v___x_4870_ == 0)
{
lean_object* v___x_4871_; 
lean_dec(v_i_4868_);
v___x_4871_ = lean_box(0);
return v___x_4871_;
}
else
{
uint8_t v___x_4872_; uint8_t v___x_4873_; uint8_t v___x_4874_; 
v___x_4872_ = lean_byte_array_fget(v_a_4867_, v_i_4868_);
v___x_4873_ = 0;
v___x_4874_ = lean_uint8_dec_eq(v___x_4872_, v___x_4873_);
if (v___x_4874_ == 0)
{
uint8_t v___x_4875_; uint8_t v___x_4876_; 
v___x_4875_ = 10;
v___x_4876_ = lean_uint8_dec_eq(v___x_4872_, v___x_4875_);
if (v___x_4876_ == 0)
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4877_ = lean_unsigned_to_nat(1u);
v___x_4878_ = lean_nat_add(v_i_4868_, v___x_4877_);
lean_dec(v_i_4868_);
v_i_4868_ = v___x_4878_;
goto _start;
}
else
{
lean_object* v___x_4880_; 
v___x_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4880_, 0, v_i_4868_);
return v___x_4880_;
}
}
else
{
lean_object* v___x_4881_; 
v___x_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4881_, 0, v_i_4868_);
return v___x_4881_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0___boxed(lean_object* v_a_4882_, lean_object* v_i_4883_){
_start:
{
lean_object* v_res_4884_; 
v_res_4884_ = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(v_a_4882_, v_i_4883_);
lean_dec_ref(v_a_4882_);
return v_res_4884_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3(lean_object* v_r_4888_){
_start:
{
lean_object* v___x_4890_; lean_object* v_data_4891_; lean_object* v_pos_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4916_; 
v___x_4890_ = lean_st_ref_take(v_r_4888_);
v_data_4891_ = lean_ctor_get(v___x_4890_, 0);
v_pos_4892_ = lean_ctor_get(v___x_4890_, 1);
v_isSharedCheck_4916_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4894_ = v___x_4890_;
v_isShared_4895_ = v_isSharedCheck_4916_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_pos_4892_);
lean_inc(v_data_4891_);
lean_dec(v___x_4890_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4916_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___y_4897_; lean_object* v___x_4908_; 
lean_inc(v_pos_4892_);
v___x_4908_ = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(v_data_4891_, v_pos_4892_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v___x_4909_; 
v___x_4909_ = lean_byte_array_size(v_data_4891_);
v___y_4897_ = v___x_4909_;
goto v___jp_4896_;
}
else
{
lean_object* v_val_4910_; uint8_t v___x_4911_; uint8_t v___x_4912_; uint8_t v___x_4913_; 
v_val_4910_ = lean_ctor_get(v___x_4908_, 0);
lean_inc(v_val_4910_);
lean_dec_ref_known(v___x_4908_, 1);
v___x_4911_ = lean_byte_array_get(v_data_4891_, v_val_4910_);
v___x_4912_ = 0;
v___x_4913_ = lean_uint8_dec_eq(v___x_4911_, v___x_4912_);
if (v___x_4913_ == 0)
{
lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4914_ = lean_unsigned_to_nat(1u);
v___x_4915_ = lean_nat_add(v_val_4910_, v___x_4914_);
lean_dec(v_val_4910_);
v___y_4897_ = v___x_4915_;
goto v___jp_4896_;
}
else
{
v___y_4897_ = v_val_4910_;
goto v___jp_4896_;
}
}
v___jp_4896_:
{
lean_object* v___x_4898_; lean_object* v___x_4900_; 
v___x_4898_ = l_ByteArray_extract(v_data_4891_, v_pos_4892_, v___y_4897_);
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 1, v___y_4897_);
v___x_4900_ = v___x_4894_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_data_4891_);
lean_ctor_set(v_reuseFailAlloc_4907_, 1, v___y_4897_);
v___x_4900_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
lean_object* v___x_4901_; uint8_t v___x_4902_; 
v___x_4901_ = lean_st_ref_put(v_r_4888_, v___x_4900_);
v___x_4902_ = lean_string_validate_utf8(v___x_4898_);
if (v___x_4902_ == 0)
{
lean_object* v___x_4903_; lean_object* v___x_4904_; 
lean_dec_ref(v___x_4898_);
v___x_4903_ = ((lean_object*)(l_IO_FS_Stream_ofBuffer___lam__3___closed__1));
v___x_4904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4903_);
return v___x_4904_;
}
else
{
lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4905_ = lean_string_from_utf8_unchecked(v___x_4898_);
v___x_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4906_, 0, v___x_4905_);
return v___x_4906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3___boxed(lean_object* v_r_4917_, lean_object* v___y_4918_){
_start:
{
lean_object* v_res_4919_; 
v_res_4919_ = l_IO_FS_Stream_ofBuffer___lam__3(v_r_4917_);
lean_dec(v_r_4917_);
return v_res_4919_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4(lean_object* v___x_4920_){
_start:
{
lean_object* v___x_4922_; 
v___x_4922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4922_, 0, v___x_4920_);
return v___x_4922_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4___boxed(lean_object* v___x_4923_, lean_object* v___y_4924_){
_start:
{
lean_object* v_res_4925_; 
v_res_4925_ = l_IO_FS_Stream_ofBuffer___lam__4(v___x_4923_);
return v_res_4925_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object* v_r_4928_){
_start:
{
lean_object* v___f_4929_; lean_object* v___f_4930_; lean_object* v___f_4931_; lean_object* v___f_4932_; lean_object* v___f_4933_; lean_object* v___f_4934_; lean_object* v___x_4935_; 
lean_inc_n(v_r_4928_, 3);
v___f_4929_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4929_, 0, v_r_4928_);
v___f_4930_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4930_, 0, v_r_4928_);
v___f_4931_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4931_, 0, v_r_4928_);
v___f_4932_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__3___boxed), 2, 1);
lean_closure_set(v___f_4932_, 0, v_r_4928_);
v___f_4933_ = ((lean_object*)(l_IO_FS_Stream_ofBuffer___closed__0));
v___f_4934_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___closed__5));
v___x_4935_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4935_, 0, v___f_4933_);
lean_ctor_set(v___x_4935_, 1, v___f_4929_);
lean_ctor_set(v___x_4935_, 2, v___f_4930_);
lean_ctor_set(v___x_4935_, 3, v___f_4932_);
lean_ctor_set(v___x_4935_, 4, v___f_4931_);
lean_ctor_set(v___x_4935_, 5, v___f_4934_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(lean_object* v_s_4938_, lean_object* v_acc_4939_){
_start:
{
lean_object* v_read_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
v_read_4941_ = lean_ctor_get(v_s_4938_, 1);
v___x_4942_ = ((lean_object*)(l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1));
lean_inc_ref(v_read_4941_);
v___x_4943_ = lean_apply_2(v_read_4941_, v___x_4942_, lean_box(0));
if (lean_obj_tag(v___x_4943_) == 0)
{
lean_object* v_a_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4957_; 
v_a_4944_ = lean_ctor_get(v___x_4943_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4943_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4946_ = v___x_4943_;
v_isShared_4947_ = v_isSharedCheck_4957_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_a_4944_);
lean_dec(v___x_4943_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4957_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
uint8_t v___x_4948_; 
v___x_4948_ = l_ByteArray_isEmpty(v_a_4944_);
if (v___x_4948_ == 0)
{
lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
lean_del_object(v___x_4946_);
v___x_4949_ = lean_unsigned_to_nat(0u);
v___x_4950_ = lean_byte_array_size(v_acc_4939_);
v___x_4951_ = lean_byte_array_size(v_a_4944_);
v___x_4952_ = lean_byte_array_copy_slice(v_a_4944_, v___x_4949_, v_acc_4939_, v___x_4950_, v___x_4951_, v___x_4948_);
lean_dec(v_a_4944_);
v_acc_4939_ = v___x_4952_;
goto _start;
}
else
{
lean_object* v___x_4955_; 
lean_dec(v_a_4944_);
lean_dec_ref(v_s_4938_);
if (v_isShared_4947_ == 0)
{
lean_ctor_set(v___x_4946_, 0, v_acc_4939_);
v___x_4955_ = v___x_4946_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_acc_4939_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
return v___x_4955_;
}
}
}
}
else
{
lean_dec_ref(v_acc_4939_);
lean_dec_ref(v_s_4938_);
return v___x_4943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed(lean_object* v_s_4958_, lean_object* v_acc_4959_, lean_object* v_a_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4958_, v_acc_4959_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto(lean_object* v_s_4962_, lean_object* v_buf_4963_){
_start:
{
lean_object* v___x_4965_; 
v___x_4965_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4962_, v_buf_4963_);
return v___x_4965_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto___boxed(lean_object* v_s_4966_, lean_object* v_buf_4967_, lean_object* v_a_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_IO_FS_Stream_readBinToEndInto(v_s_4966_, v_buf_4967_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd(lean_object* v_s_4970_){
_start:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; 
v___x_4972_ = l_ByteArray_empty;
v___x_4973_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4970_, v___x_4972_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd___boxed(lean_object* v_s_4974_, lean_object* v_a_4975_){
_start:
{
lean_object* v_res_4976_; 
v_res_4976_ = l_IO_FS_Stream_readBinToEnd(v_s_4974_);
return v_res_4976_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd(lean_object* v_s_4980_){
_start:
{
lean_object* v___x_4982_; 
v___x_4982_ = l_IO_FS_Stream_readBinToEnd(v_s_4980_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4996_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4985_ = v___x_4982_;
v_isShared_4986_ = v_isSharedCheck_4996_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_a_4983_);
lean_dec(v___x_4982_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4996_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
uint8_t v___x_4987_; 
v___x_4987_ = lean_string_validate_utf8(v_a_4983_);
if (v___x_4987_ == 0)
{
lean_object* v___x_4988_; lean_object* v___x_4990_; 
lean_dec(v_a_4983_);
v___x_4988_ = ((lean_object*)(l_IO_FS_Stream_readToEnd___closed__1));
if (v_isShared_4986_ == 0)
{
lean_ctor_set_tag(v___x_4985_, 1);
lean_ctor_set(v___x_4985_, 0, v___x_4988_);
v___x_4990_ = v___x_4985_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v___x_4988_);
v___x_4990_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
return v___x_4990_;
}
}
else
{
lean_object* v___x_4992_; lean_object* v___x_4994_; 
v___x_4992_ = lean_string_from_utf8_unchecked(v_a_4983_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v___x_4992_);
v___x_4994_ = v___x_4985_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v___x_4992_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
else
{
lean_object* v_a_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5004_; 
v_a_4997_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4999_ = v___x_4982_;
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_a_4997_);
lean_dec(v___x_4982_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v___x_5002_; 
if (v_isShared_5000_ == 0)
{
v___x_5002_ = v___x_4999_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_a_4997_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd___boxed(lean_object* v_s_5005_, lean_object* v_a_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l_IO_FS_Stream_readToEnd(v_s_5005_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read(lean_object* v_s_5008_, lean_object* v_lines_5009_){
_start:
{
lean_object* v_getLine_5011_; lean_object* v___x_5012_; 
v_getLine_5011_ = lean_ctor_get(v_s_5008_, 3);
lean_inc_ref(v_getLine_5011_);
v___x_5012_ = lean_apply_1(v_getLine_5011_, lean_box(0));
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5070_; 
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5070_ == 0)
{
v___x_5015_ = v___x_5012_;
v_isShared_5016_ = v_isSharedCheck_5070_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_5012_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5070_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___y_5018_; lean_object* v___y_5022_; lean_object* v___y_5023_; lean_object* v___y_5024_; uint32_t v___y_5025_; lean_object* v___y_5033_; lean_object* v___y_5034_; lean_object* v___y_5035_; uint32_t v___y_5038_; lean_object* v___x_5060_; lean_object* v___x_5061_; uint8_t v___x_5062_; 
v___x_5060_ = lean_string_utf8_byte_size(v_a_5013_);
v___x_5061_ = lean_unsigned_to_nat(0u);
v___x_5062_ = lean_nat_dec_eq(v___x_5060_, v___x_5061_);
if (v___x_5062_ == 0)
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
lean_inc(v_a_5013_);
v___x_5063_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5063_, 0, v_a_5013_);
lean_ctor_set(v___x_5063_, 1, v___x_5061_);
lean_ctor_set(v___x_5063_, 2, v___x_5060_);
v___x_5064_ = l_String_Slice_Pos_prev_x3f(v___x_5063_, v___x_5060_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_dec_ref_known(v___x_5063_, 3);
goto v___jp_5058_;
}
else
{
lean_object* v_val_5065_; lean_object* v___x_5066_; 
v_val_5065_ = lean_ctor_get(v___x_5064_, 0);
lean_inc(v_val_5065_);
lean_dec_ref_known(v___x_5064_, 1);
v___x_5066_ = l_String_Slice_Pos_get_x3f(v___x_5063_, v_val_5065_);
lean_dec(v_val_5065_);
lean_dec_ref_known(v___x_5063_, 3);
if (lean_obj_tag(v___x_5066_) == 0)
{
goto v___jp_5058_;
}
else
{
lean_object* v_val_5067_; uint32_t v___x_5068_; 
v_val_5067_ = lean_ctor_get(v___x_5066_, 0);
lean_inc(v_val_5067_);
lean_dec_ref_known(v___x_5066_, 1);
v___x_5068_ = lean_unbox_uint32(v_val_5067_);
lean_dec(v_val_5067_);
v___y_5038_ = v___x_5068_;
goto v___jp_5037_;
}
}
}
else
{
lean_object* v___x_5069_; 
lean_del_object(v___x_5015_);
lean_dec(v_a_5013_);
lean_dec_ref(v_s_5008_);
v___x_5069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5069_, 0, v_lines_5009_);
return v___x_5069_;
}
v___jp_5017_:
{
lean_object* v___x_5019_; 
v___x_5019_ = lean_array_push(v_lines_5009_, v___y_5018_);
v_lines_5009_ = v___x_5019_;
goto _start;
}
v___jp_5021_:
{
uint32_t v___x_5026_; uint8_t v___x_5027_; 
v___x_5026_ = 13;
v___x_5027_ = lean_uint32_dec_eq(v___y_5025_, v___x_5026_);
if (v___x_5027_ == 0)
{
lean_dec(v___y_5023_);
lean_dec(v___y_5022_);
v___y_5018_ = v___y_5024_;
goto v___jp_5017_;
}
else
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5028_ = lean_string_utf8_byte_size(v___y_5024_);
lean_inc(v___y_5022_);
lean_inc_ref(v___y_5024_);
v___x_5029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5029_, 0, v___y_5024_);
lean_ctor_set(v___x_5029_, 1, v___y_5022_);
lean_ctor_set(v___x_5029_, 2, v___x_5028_);
v___x_5030_ = l_String_Slice_Pos_prevn(v___x_5029_, v___x_5028_, v___y_5023_);
lean_dec_ref_known(v___x_5029_, 3);
v___x_5031_ = lean_string_utf8_extract_fast(v___y_5024_, v___y_5022_, v___x_5030_);
lean_dec(v___x_5030_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5024_);
v___y_5018_ = v___x_5031_;
goto v___jp_5017_;
}
}
v___jp_5032_:
{
uint32_t v___x_5036_; 
v___x_5036_ = 65;
v___y_5022_ = v___y_5033_;
v___y_5023_ = v___y_5034_;
v___y_5024_ = v___y_5035_;
v___y_5025_ = v___x_5036_;
goto v___jp_5021_;
}
v___jp_5037_:
{
uint32_t v___x_5039_; uint8_t v___x_5040_; 
v___x_5039_ = 10;
v___x_5040_ = lean_uint32_dec_eq(v___y_5038_, v___x_5039_);
if (v___x_5040_ == 0)
{
lean_object* v___x_5041_; lean_object* v___x_5043_; 
lean_dec_ref(v_s_5008_);
v___x_5041_ = lean_array_push(v_lines_5009_, v_a_5013_);
if (v_isShared_5016_ == 0)
{
lean_ctor_set(v___x_5015_, 0, v___x_5041_);
v___x_5043_ = v___x_5015_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v___x_5041_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
else
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
lean_del_object(v___x_5015_);
v___x_5045_ = lean_unsigned_to_nat(1u);
v___x_5046_ = lean_unsigned_to_nat(0u);
v___x_5047_ = lean_string_utf8_byte_size(v_a_5013_);
lean_inc(v_a_5013_);
v___x_5048_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5048_, 0, v_a_5013_);
lean_ctor_set(v___x_5048_, 1, v___x_5046_);
lean_ctor_set(v___x_5048_, 2, v___x_5047_);
v___x_5049_ = l_String_Slice_Pos_prevn(v___x_5048_, v___x_5047_, v___x_5045_);
lean_dec_ref_known(v___x_5048_, 3);
v___x_5050_ = lean_string_utf8_extract_fast(v_a_5013_, v___x_5046_, v___x_5049_);
lean_dec(v___x_5049_);
lean_dec(v_a_5013_);
v___x_5051_ = lean_string_utf8_byte_size(v___x_5050_);
lean_inc_ref(v___x_5050_);
v___x_5052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5050_);
lean_ctor_set(v___x_5052_, 1, v___x_5046_);
lean_ctor_set(v___x_5052_, 2, v___x_5051_);
v___x_5053_ = l_String_Slice_Pos_prev_x3f(v___x_5052_, v___x_5051_);
if (lean_obj_tag(v___x_5053_) == 0)
{
lean_dec_ref_known(v___x_5052_, 3);
v___y_5033_ = v___x_5046_;
v___y_5034_ = v___x_5045_;
v___y_5035_ = v___x_5050_;
goto v___jp_5032_;
}
else
{
lean_object* v_val_5054_; lean_object* v___x_5055_; 
v_val_5054_ = lean_ctor_get(v___x_5053_, 0);
lean_inc(v_val_5054_);
lean_dec_ref_known(v___x_5053_, 1);
v___x_5055_ = l_String_Slice_Pos_get_x3f(v___x_5052_, v_val_5054_);
lean_dec(v_val_5054_);
lean_dec_ref_known(v___x_5052_, 3);
if (lean_obj_tag(v___x_5055_) == 0)
{
v___y_5033_ = v___x_5046_;
v___y_5034_ = v___x_5045_;
v___y_5035_ = v___x_5050_;
goto v___jp_5032_;
}
else
{
lean_object* v_val_5056_; uint32_t v___x_5057_; 
v_val_5056_ = lean_ctor_get(v___x_5055_, 0);
lean_inc(v_val_5056_);
lean_dec_ref_known(v___x_5055_, 1);
v___x_5057_ = lean_unbox_uint32(v_val_5056_);
lean_dec(v_val_5056_);
v___y_5022_ = v___x_5046_;
v___y_5023_ = v___x_5045_;
v___y_5024_ = v___x_5050_;
v___y_5025_ = v___x_5057_;
goto v___jp_5021_;
}
}
}
}
v___jp_5058_:
{
uint32_t v___x_5059_; 
v___x_5059_ = 65;
v___y_5038_ = v___x_5059_;
goto v___jp_5037_;
}
}
}
else
{
lean_object* v_a_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5078_; 
lean_dec_ref(v_lines_5009_);
lean_dec_ref(v_s_5008_);
v_a_5071_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5073_ = v___x_5012_;
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_a_5071_);
lean_dec(v___x_5012_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5078_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5076_; 
if (v_isShared_5074_ == 0)
{
v___x_5076_ = v___x_5073_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5071_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read___boxed(lean_object* v_s_5079_, lean_object* v_lines_5080_, lean_object* v_a_5081_){
_start:
{
lean_object* v_res_5082_; 
v_res_5082_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_5079_, v_lines_5080_);
return v_res_5082_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines(lean_object* v_s_5083_){
_start:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5085_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_5086_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_5083_, v___x_5085_);
return v___x_5086_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines___boxed(lean_object* v_s_5087_, lean_object* v_a_5088_){
_start:
{
lean_object* v_res_5089_; 
v_res_5089_ = l_IO_FS_Stream_lines(v_s_5087_);
return v_res_5089_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0(lean_object* v_bOut_5090_){
_start:
{
lean_object* v___x_5092_; 
v___x_5092_ = lean_st_ref_get(v_bOut_5090_);
return v___x_5092_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed(lean_object* v_bOut_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l_IO_FS_withIsolatedStreams___redArg___lam__0(v_bOut_5093_);
lean_dec(v_bOut_5093_);
return v_res_5095_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5100_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3));
v___x_5101_ = lean_unsigned_to_nat(46u);
v___x_5102_ = lean_unsigned_to_nat(193u);
v___x_5103_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2));
v___x_5104_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1));
v___x_5105_ = l_mkPanicMessageWithDecl(v___x_5104_, v___x_5103_, v___x_5102_, v___x_5101_, v___x_5100_);
return v___x_5105_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1(lean_object* v_r_5106_, lean_object* v_toPure_5107_, lean_object* v_bOut_5108_){
_start:
{
lean_object* v___y_5110_; lean_object* v_data_5113_; uint8_t v___x_5114_; 
v_data_5113_ = lean_ctor_get(v_bOut_5108_, 0);
lean_inc_ref(v_data_5113_);
lean_dec_ref(v_bOut_5108_);
v___x_5114_ = lean_string_validate_utf8(v_data_5113_);
if (v___x_5114_ == 0)
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; 
lean_dec_ref(v_data_5113_);
v___x_5115_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0));
v___x_5116_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4, &l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4_once, _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4);
v___x_5117_ = l_panic___redArg(v___x_5115_, v___x_5116_);
v___y_5110_ = v___x_5117_;
goto v___jp_5109_;
}
else
{
lean_object* v___x_5118_; 
v___x_5118_ = lean_string_from_utf8_unchecked(v_data_5113_);
v___y_5110_ = v___x_5118_;
goto v___jp_5109_;
}
v___jp_5109_:
{
lean_object* v___x_5111_; lean_object* v___x_5112_; 
v___x_5111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5111_, 0, v___y_5110_);
lean_ctor_set(v___x_5111_, 1, v_r_5106_);
v___x_5112_ = lean_apply_2(v_toPure_5107_, lean_box(0), v___x_5111_);
return v___x_5112_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__2(lean_object* v_toPure_5119_, lean_object* v_inst_5120_, lean_object* v___f_5121_, lean_object* v_toBind_5122_, lean_object* v_r_5123_){
_start:
{
lean_object* v___f_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; 
v___f_5124_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5124_, 0, v_r_5123_);
lean_closure_set(v___f_5124_, 1, v_toPure_5119_);
v___x_5125_ = lean_apply_2(v_inst_5120_, lean_box(0), v___f_5121_);
v___x_5126_ = lean_apply_4(v_toBind_5122_, lean_box(0), lean_box(0), v___x_5125_, v___f_5124_);
return v___x_5126_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3(lean_object* v_toPure_5127_, lean_object* v_inst_5128_, lean_object* v_toBind_5129_, lean_object* v_bIn_5130_, lean_object* v_inst_5131_, lean_object* v_inst_5132_, uint8_t v_isolateStderr_5133_, lean_object* v_x_5134_, lean_object* v_bOut_5135_){
_start:
{
lean_object* v___f_5136_; lean_object* v___f_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___y_5141_; 
lean_inc(v_bOut_5135_);
v___f_5136_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5136_, 0, v_bOut_5135_);
lean_inc(v_toBind_5129_);
lean_inc(v_inst_5128_);
v___f_5137_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__2), 5, 4);
lean_closure_set(v___f_5137_, 0, v_toPure_5127_);
lean_closure_set(v___f_5137_, 1, v_inst_5128_);
lean_closure_set(v___f_5137_, 2, v___f_5136_);
lean_closure_set(v___f_5137_, 3, v_toBind_5129_);
v___x_5138_ = l_IO_FS_Stream_ofBuffer(v_bIn_5130_);
v___x_5139_ = l_IO_FS_Stream_ofBuffer(v_bOut_5135_);
if (v_isolateStderr_5133_ == 0)
{
v___y_5141_ = v_x_5134_;
goto v___jp_5140_;
}
else
{
lean_object* v___x_5145_; 
lean_inc_ref(v___x_5139_);
lean_inc(v_inst_5128_);
lean_inc(v_inst_5132_);
lean_inc_ref(v_inst_5131_);
v___x_5145_ = l_IO_withStderr___redArg(v_inst_5131_, v_inst_5132_, v_inst_5128_, v___x_5139_, v_x_5134_);
v___y_5141_ = v___x_5145_;
goto v___jp_5140_;
}
v___jp_5140_:
{
lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; 
lean_inc(v_inst_5128_);
lean_inc(v_inst_5132_);
lean_inc_ref(v_inst_5131_);
v___x_5142_ = l_IO_withStdout___redArg(v_inst_5131_, v_inst_5132_, v_inst_5128_, v___x_5139_, v___y_5141_);
v___x_5143_ = l_IO_withStdin___redArg(v_inst_5131_, v_inst_5132_, v_inst_5128_, v___x_5138_, v___x_5142_);
v___x_5144_ = lean_apply_4(v_toBind_5129_, lean_box(0), lean_box(0), v___x_5143_, v___f_5137_);
return v___x_5144_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed(lean_object* v_toPure_5146_, lean_object* v_inst_5147_, lean_object* v_toBind_5148_, lean_object* v_bIn_5149_, lean_object* v_inst_5150_, lean_object* v_inst_5151_, lean_object* v_isolateStderr_5152_, lean_object* v_x_5153_, lean_object* v_bOut_5154_){
_start:
{
uint8_t v_isolateStderr_boxed_5155_; lean_object* v_res_5156_; 
v_isolateStderr_boxed_5155_ = lean_unbox(v_isolateStderr_5152_);
v_res_5156_ = l_IO_FS_withIsolatedStreams___redArg___lam__3(v_toPure_5146_, v_inst_5147_, v_toBind_5148_, v_bIn_5149_, v_inst_5150_, v_inst_5151_, v_isolateStderr_boxed_5155_, v_x_5153_, v_bOut_5154_);
return v_res_5156_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4(lean_object* v_toPure_5157_, lean_object* v_inst_5158_, lean_object* v_toBind_5159_, lean_object* v_inst_5160_, lean_object* v_inst_5161_, uint8_t v_isolateStderr_5162_, lean_object* v_x_5163_, lean_object* v___x_5164_, lean_object* v_bIn_5165_){
_start:
{
lean_object* v___x_5166_; lean_object* v___f_5167_; lean_object* v___x_5168_; 
v___x_5166_ = lean_box(v_isolateStderr_5162_);
lean_inc(v_toBind_5159_);
v___f_5167_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_5167_, 0, v_toPure_5157_);
lean_closure_set(v___f_5167_, 1, v_inst_5158_);
lean_closure_set(v___f_5167_, 2, v_toBind_5159_);
lean_closure_set(v___f_5167_, 3, v_bIn_5165_);
lean_closure_set(v___f_5167_, 4, v_inst_5160_);
lean_closure_set(v___f_5167_, 5, v_inst_5161_);
lean_closure_set(v___f_5167_, 6, v___x_5166_);
lean_closure_set(v___f_5167_, 7, v_x_5163_);
v___x_5168_ = lean_apply_4(v_toBind_5159_, lean_box(0), lean_box(0), v___x_5164_, v___f_5167_);
return v___x_5168_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed(lean_object* v_toPure_5169_, lean_object* v_inst_5170_, lean_object* v_toBind_5171_, lean_object* v_inst_5172_, lean_object* v_inst_5173_, lean_object* v_isolateStderr_5174_, lean_object* v_x_5175_, lean_object* v___x_5176_, lean_object* v_bIn_5177_){
_start:
{
uint8_t v_isolateStderr_boxed_5178_; lean_object* v_res_5179_; 
v_isolateStderr_boxed_5178_ = lean_unbox(v_isolateStderr_5174_);
v_res_5179_ = l_IO_FS_withIsolatedStreams___redArg___lam__4(v_toPure_5169_, v_inst_5170_, v_toBind_5171_, v_inst_5172_, v_inst_5173_, v_isolateStderr_boxed_5178_, v_x_5175_, v___x_5176_, v_bIn_5177_);
return v_res_5179_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__0(void){
_start:
{
lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; 
v___x_5180_ = lean_unsigned_to_nat(0u);
v___x_5181_ = l_ByteArray_empty;
v___x_5182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5182_, 0, v___x_5181_);
lean_ctor_set(v___x_5182_, 1, v___x_5180_);
return v___x_5182_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__1(void){
_start:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; 
v___x_5183_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___closed__0, &l_IO_FS_withIsolatedStreams___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___redArg___closed__0);
v___x_5184_ = lean_alloc_closure((void*)(l_IO_mkRef___boxed), 3, 2);
lean_closure_set(v___x_5184_, 0, lean_box(0));
lean_closure_set(v___x_5184_, 1, v___x_5183_);
return v___x_5184_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object* v_inst_5185_, lean_object* v_inst_5186_, lean_object* v_inst_5187_, lean_object* v_x_5188_, uint8_t v_isolateStderr_5189_){
_start:
{
lean_object* v_toApplicative_5190_; lean_object* v_toBind_5191_; lean_object* v_toPure_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___f_5196_; lean_object* v___x_5197_; 
v_toApplicative_5190_ = lean_ctor_get(v_inst_5185_, 0);
v_toBind_5191_ = lean_ctor_get(v_inst_5185_, 1);
lean_inc_n(v_toBind_5191_, 2);
v_toPure_5192_ = lean_ctor_get(v_toApplicative_5190_, 1);
lean_inc(v_toPure_5192_);
v___x_5193_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___closed__1, &l_IO_FS_withIsolatedStreams___redArg___closed__1_once, _init_l_IO_FS_withIsolatedStreams___redArg___closed__1);
lean_inc(v_inst_5187_);
v___x_5194_ = lean_apply_2(v_inst_5187_, lean_box(0), v___x_5193_);
v___x_5195_ = lean_box(v_isolateStderr_5189_);
lean_inc(v___x_5194_);
v___f_5196_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_5196_, 0, v_toPure_5192_);
lean_closure_set(v___f_5196_, 1, v_inst_5187_);
lean_closure_set(v___f_5196_, 2, v_toBind_5191_);
lean_closure_set(v___f_5196_, 3, v_inst_5185_);
lean_closure_set(v___f_5196_, 4, v_inst_5186_);
lean_closure_set(v___f_5196_, 5, v___x_5195_);
lean_closure_set(v___f_5196_, 6, v_x_5188_);
lean_closure_set(v___f_5196_, 7, v___x_5194_);
v___x_5197_ = lean_apply_4(v_toBind_5191_, lean_box(0), lean_box(0), v___x_5194_, v___f_5196_);
return v___x_5197_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___boxed(lean_object* v_inst_5198_, lean_object* v_inst_5199_, lean_object* v_inst_5200_, lean_object* v_x_5201_, lean_object* v_isolateStderr_5202_){
_start:
{
uint8_t v_isolateStderr_boxed_5203_; lean_object* v_res_5204_; 
v_isolateStderr_boxed_5203_ = lean_unbox(v_isolateStderr_5202_);
v_res_5204_ = l_IO_FS_withIsolatedStreams___redArg(v_inst_5198_, v_inst_5199_, v_inst_5200_, v_x_5201_, v_isolateStderr_boxed_5203_);
return v_res_5204_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object* v_m_5205_, lean_object* v_00_u03b1_5206_, lean_object* v_inst_5207_, lean_object* v_inst_5208_, lean_object* v_inst_5209_, lean_object* v_x_5210_, uint8_t v_isolateStderr_5211_){
_start:
{
lean_object* v___x_5212_; 
v___x_5212_ = l_IO_FS_withIsolatedStreams___redArg(v_inst_5207_, v_inst_5208_, v_inst_5209_, v_x_5210_, v_isolateStderr_5211_);
return v___x_5212_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___boxed(lean_object* v_m_5213_, lean_object* v_00_u03b1_5214_, lean_object* v_inst_5215_, lean_object* v_inst_5216_, lean_object* v_inst_5217_, lean_object* v_x_5218_, lean_object* v_isolateStderr_5219_){
_start:
{
uint8_t v_isolateStderr_boxed_5220_; lean_object* v_res_5221_; 
v_isolateStderr_boxed_5220_ = lean_unbox(v_isolateStderr_5219_);
v_res_5221_ = l_IO_FS_withIsolatedStreams(v_m_5213_, v_00_u03b1_5214_, v_inst_5215_, v_inst_5216_, v_inst_5217_, v_x_5218_, v_isolateStderr_boxed_5220_);
return v_res_5221_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9(void){
_start:
{
lean_object* v___x_5278_; lean_object* v___x_5279_; 
v___x_5278_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0));
v___x_5279_ = l_String_toRawSubstring_x27(v___x_5278_);
return v___x_5279_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17(void){
_start:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; 
v___x_5294_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16));
v___x_5295_ = l_String_toRawSubstring_x27(v___x_5294_);
return v___x_5295_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24(void){
_start:
{
lean_object* v___x_5308_; lean_object* v___x_5309_; 
v___x_5308_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18));
v___x_5309_ = l_String_toRawSubstring_x27(v___x_5308_);
return v___x_5309_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31(void){
_start:
{
lean_object* v___x_5324_; lean_object* v___x_5325_; 
v___x_5324_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30));
v___x_5325_ = l_String_toRawSubstring_x27(v___x_5324_);
return v___x_5325_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object* v_x_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_){
_start:
{
lean_object* v___x_5353_; uint8_t v___x_5354_; 
v___x_5353_ = ((lean_object*)(l_termPrintln_x21_____00__closed__1));
lean_inc(v_x_5350_);
v___x_5354_ = l_Lean_Syntax_isOfKind(v_x_5350_, v___x_5353_);
if (v___x_5354_ == 0)
{
lean_object* v___x_5355_; lean_object* v___x_5356_; 
lean_dec(v_x_5350_);
v___x_5355_ = lean_box(1);
v___x_5356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5356_, 0, v___x_5355_);
lean_ctor_set(v___x_5356_, 1, v_a_5352_);
return v___x_5356_;
}
else
{
lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; uint8_t v___x_5360_; 
v___x_5357_ = lean_unsigned_to_nat(1u);
v___x_5358_ = l_Lean_Syntax_getArg(v_x_5350_, v___x_5357_);
lean_dec(v_x_5350_);
v___x_5359_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1));
lean_inc(v___x_5358_);
v___x_5360_ = l_Lean_Syntax_isOfKind(v___x_5358_, v___x_5359_);
if (v___x_5360_ == 0)
{
lean_object* v_quotContext_5361_; lean_object* v_currMacroScope_5362_; lean_object* v_ref_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; 
v_quotContext_5361_ = lean_ctor_get(v_a_5351_, 1);
v_currMacroScope_5362_ = lean_ctor_get(v_a_5351_, 2);
v_ref_5363_ = lean_ctor_get(v_a_5351_, 5);
v___x_5364_ = l_Lean_SourceInfo_fromRef(v_ref_5363_, v___x_5360_);
v___x_5365_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3));
v___x_5366_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5));
v___x_5367_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6));
lean_inc_n(v___x_5364_, 14);
v___x_5368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5368_, 0, v___x_5364_);
lean_ctor_set(v___x_5368_, 1, v___x_5367_);
v___x_5369_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8));
v___x_5370_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
v___x_5371_ = lean_box(0);
lean_inc_n(v_currMacroScope_5362_, 4);
lean_inc_n(v_quotContext_5361_, 4);
v___x_5372_ = l_Lean_addMacroScope(v_quotContext_5361_, v___x_5371_, v_currMacroScope_5362_);
v___x_5373_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15));
v___x_5374_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5374_, 0, v___x_5364_);
lean_ctor_set(v___x_5374_, 1, v___x_5370_);
lean_ctor_set(v___x_5374_, 2, v___x_5372_);
lean_ctor_set(v___x_5374_, 3, v___x_5373_);
v___x_5375_ = l_Lean_Syntax_node1(v___x_5364_, v___x_5369_, v___x_5374_);
v___x_5376_ = l_Lean_Syntax_node2(v___x_5364_, v___x_5366_, v___x_5368_, v___x_5375_);
v___x_5377_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_5378_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
v___x_5379_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20));
v___x_5380_ = l_Lean_addMacroScope(v_quotContext_5361_, v___x_5379_, v_currMacroScope_5362_);
v___x_5381_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22));
v___x_5382_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5382_, 0, v___x_5364_);
lean_ctor_set(v___x_5382_, 1, v___x_5378_);
lean_ctor_set(v___x_5382_, 2, v___x_5380_);
lean_ctor_set(v___x_5382_, 3, v___x_5381_);
v___x_5383_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_5384_ = l_Lean_Syntax_node1(v___x_5364_, v___x_5383_, v___x_5358_);
v___x_5385_ = l_Lean_Syntax_node2(v___x_5364_, v___x_5377_, v___x_5382_, v___x_5384_);
v___x_5386_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23));
v___x_5387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5387_, 0, v___x_5364_);
lean_ctor_set(v___x_5387_, 1, v___x_5386_);
v___x_5388_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
v___x_5389_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25));
v___x_5390_ = l_Lean_addMacroScope(v_quotContext_5361_, v___x_5389_, v_currMacroScope_5362_);
v___x_5391_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29));
v___x_5392_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5392_, 0, v___x_5364_);
lean_ctor_set(v___x_5392_, 1, v___x_5388_);
lean_ctor_set(v___x_5392_, 2, v___x_5390_);
lean_ctor_set(v___x_5392_, 3, v___x_5391_);
v___x_5393_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
v___x_5394_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32));
v___x_5395_ = l_Lean_addMacroScope(v_quotContext_5361_, v___x_5394_, v_currMacroScope_5362_);
v___x_5396_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36));
v___x_5397_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5397_, 0, v___x_5364_);
lean_ctor_set(v___x_5397_, 1, v___x_5393_);
lean_ctor_set(v___x_5397_, 2, v___x_5395_);
lean_ctor_set(v___x_5397_, 3, v___x_5396_);
v___x_5398_ = l_Lean_Syntax_node1(v___x_5364_, v___x_5383_, v___x_5397_);
v___x_5399_ = l_Lean_Syntax_node2(v___x_5364_, v___x_5377_, v___x_5392_, v___x_5398_);
v___x_5400_ = l_Lean_Syntax_node1(v___x_5364_, v___x_5383_, v___x_5399_);
v___x_5401_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37));
v___x_5402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5364_);
lean_ctor_set(v___x_5402_, 1, v___x_5401_);
v___x_5403_ = l_Lean_Syntax_node5(v___x_5364_, v___x_5365_, v___x_5376_, v___x_5385_, v___x_5387_, v___x_5400_, v___x_5402_);
v___x_5404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5404_, 0, v___x_5403_);
lean_ctor_set(v___x_5404_, 1, v_a_5352_);
return v___x_5404_;
}
else
{
lean_object* v_quotContext_5405_; lean_object* v_currMacroScope_5406_; lean_object* v_ref_5407_; uint8_t v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; 
v_quotContext_5405_ = lean_ctor_get(v_a_5351_, 1);
v_currMacroScope_5406_ = lean_ctor_get(v_a_5351_, 2);
v_ref_5407_ = lean_ctor_get(v_a_5351_, 5);
v___x_5408_ = 0;
v___x_5409_ = l_Lean_SourceInfo_fromRef(v_ref_5407_, v___x_5408_);
v___x_5410_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3));
v___x_5411_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5));
v___x_5412_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6));
lean_inc_n(v___x_5409_, 17);
v___x_5413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5413_, 0, v___x_5409_);
lean_ctor_set(v___x_5413_, 1, v___x_5412_);
v___x_5414_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8));
v___x_5415_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
v___x_5416_ = lean_box(0);
lean_inc_n(v_currMacroScope_5406_, 4);
lean_inc_n(v_quotContext_5405_, 4);
v___x_5417_ = l_Lean_addMacroScope(v_quotContext_5405_, v___x_5416_, v_currMacroScope_5406_);
v___x_5418_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15));
v___x_5419_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5419_, 0, v___x_5409_);
lean_ctor_set(v___x_5419_, 1, v___x_5415_);
lean_ctor_set(v___x_5419_, 2, v___x_5417_);
lean_ctor_set(v___x_5419_, 3, v___x_5418_);
v___x_5420_ = l_Lean_Syntax_node1(v___x_5409_, v___x_5414_, v___x_5419_);
v___x_5421_ = l_Lean_Syntax_node2(v___x_5409_, v___x_5411_, v___x_5413_, v___x_5420_);
v___x_5422_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_5423_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
v___x_5424_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20));
v___x_5425_ = l_Lean_addMacroScope(v_quotContext_5405_, v___x_5424_, v_currMacroScope_5406_);
v___x_5426_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22));
v___x_5427_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5427_, 0, v___x_5409_);
lean_ctor_set(v___x_5427_, 1, v___x_5423_);
lean_ctor_set(v___x_5427_, 2, v___x_5425_);
lean_ctor_set(v___x_5427_, 3, v___x_5426_);
v___x_5428_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_5429_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39));
v___x_5430_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41));
v___x_5431_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42));
v___x_5432_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5432_, 0, v___x_5409_);
lean_ctor_set(v___x_5432_, 1, v___x_5431_);
v___x_5433_ = l_Lean_Syntax_node2(v___x_5409_, v___x_5430_, v___x_5432_, v___x_5358_);
v___x_5434_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37));
v___x_5435_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5435_, 0, v___x_5409_);
lean_ctor_set(v___x_5435_, 1, v___x_5434_);
lean_inc_ref(v___x_5435_);
lean_inc(v___x_5421_);
v___x_5436_ = l_Lean_Syntax_node3(v___x_5409_, v___x_5429_, v___x_5421_, v___x_5433_, v___x_5435_);
v___x_5437_ = l_Lean_Syntax_node1(v___x_5409_, v___x_5428_, v___x_5436_);
v___x_5438_ = l_Lean_Syntax_node2(v___x_5409_, v___x_5422_, v___x_5427_, v___x_5437_);
v___x_5439_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23));
v___x_5440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5440_, 0, v___x_5409_);
lean_ctor_set(v___x_5440_, 1, v___x_5439_);
v___x_5441_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
v___x_5442_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25));
v___x_5443_ = l_Lean_addMacroScope(v_quotContext_5405_, v___x_5442_, v_currMacroScope_5406_);
v___x_5444_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29));
v___x_5445_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5445_, 0, v___x_5409_);
lean_ctor_set(v___x_5445_, 1, v___x_5441_);
lean_ctor_set(v___x_5445_, 2, v___x_5443_);
lean_ctor_set(v___x_5445_, 3, v___x_5444_);
v___x_5446_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
v___x_5447_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32));
v___x_5448_ = l_Lean_addMacroScope(v_quotContext_5405_, v___x_5447_, v_currMacroScope_5406_);
v___x_5449_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36));
v___x_5450_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5450_, 0, v___x_5409_);
lean_ctor_set(v___x_5450_, 1, v___x_5446_);
lean_ctor_set(v___x_5450_, 2, v___x_5448_);
lean_ctor_set(v___x_5450_, 3, v___x_5449_);
v___x_5451_ = l_Lean_Syntax_node1(v___x_5409_, v___x_5428_, v___x_5450_);
v___x_5452_ = l_Lean_Syntax_node2(v___x_5409_, v___x_5422_, v___x_5445_, v___x_5451_);
v___x_5453_ = l_Lean_Syntax_node1(v___x_5409_, v___x_5428_, v___x_5452_);
v___x_5454_ = l_Lean_Syntax_node5(v___x_5409_, v___x_5410_, v___x_5421_, v___x_5438_, v___x_5440_, v___x_5453_, v___x_5435_);
v___x_5455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5455_, 0, v___x_5454_);
lean_ctor_set(v___x_5455_, 1, v_a_5352_);
return v___x_5455_;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___boxed(lean_object* v_x_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_){
_start:
{
lean_object* v_res_5459_; 
v_res_5459_ = l___aux__Init__System__IO______macroRules__termPrintln_x21______1(v_x_5456_, v_a_5457_, v_a_5458_);
lean_dec_ref(v_a_5457_);
return v_res_5459_;
}
}
LEAN_EXPORT lean_object* l_Runtime_markMultiThreaded___boxed(lean_object* v_00_u03b1_5463_, lean_object* v_a_5464_, lean_object* v_a_00___x40___internal___hyg_5465_){
_start:
{
lean_object* v_res_5466_; 
v_res_5466_ = lean_runtime_mark_multi_threaded(v_a_5464_);
return v_res_5466_;
}
}
LEAN_EXPORT lean_object* l_Runtime_markPersistent___boxed(lean_object* v_00_u03b1_5470_, lean_object* v_a_5471_, lean_object* v_a_00___x40___internal___hyg_5472_){
_start:
{
lean_object* v_res_5473_; 
v_res_5473_ = lean_runtime_mark_persistent(v_a_5471_);
return v_res_5473_;
}
}
LEAN_EXPORT lean_object* l_Runtime_forget___boxed(lean_object* v_00_u03b1_5477_, lean_object* v_a_5478_, lean_object* v_a_00___x40___internal___hyg_5479_){
_start:
{
lean_object* v_res_5480_; 
v_res_5480_ = lean_runtime_forget(v_a_5478_);
return v_res_5480_;
}
}
LEAN_EXPORT lean_object* l_Runtime_hold___boxed(lean_object* v_00_u03b1_5484_, lean_object* v_a_5485_, lean_object* v_a_00___x40___internal___hyg_5486_){
_start:
{
lean_object* v_res_5487_; 
v_res_5487_ = lean_runtime_hold(v_a_5485_);
lean_dec(v_a_5485_);
return v_res_5487_;
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
