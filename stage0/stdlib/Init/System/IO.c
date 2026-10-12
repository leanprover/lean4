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
lean_object* l_instMonadBaseIO___aux__1___redArg(lean_object* v_f_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_apply_1(v_x_3_, lean_box(0));
v___x_6_ = lean_apply_1(v_f_2_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2_ = stack[0].m_obj;
lean_object* v_x_3_ = stack[1].m_obj;
lean_object* v_res_7_;
v_res_7_ = l_instMonadBaseIO___aux__1___redArg(v_f_2_, v_x_3_);
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__1___redArg___boxed(lean_object* v_f_8_, lean_object* v_x_9_, lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_instMonadBaseIO___aux__1___redArg(v_f_8_, v_x_9_);
return v_res_11_;
}
}
lean_object* l_instMonadBaseIO___aux__1(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_f_14_, lean_object* v_x_15_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_apply_1(v_x_15_, lean_box(0));
v___x_18_ = lean_apply_1(v_f_14_, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_14_ = stack[2].m_obj;
lean_object* v_x_15_ = stack[3].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_instMonadBaseIO___aux__1(lean_box(0), lean_box(0), v_f_14_, v_x_15_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__1___boxed(lean_object* v_00_u03b1_20_, lean_object* v_00_u03b2_21_, lean_object* v_f_22_, lean_object* v_x_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_instMonadBaseIO___aux__1(v_00_u03b1_20_, v_00_u03b2_21_, v_f_22_, v_x_23_);
return v_res_25_;
}
}
lean_object* l_instMonadBaseIO___aux__3___redArg(lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_apply_1(v_a_27_, lean_box(0));
lean_dec(v___x_29_);
lean_inc(v_a_26_);
return v_a_26_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_26_ = stack[0].m_obj;
lean_object* v_a_27_ = stack[1].m_obj;
lean_object* v_res_30_;
v_res_30_ = l_instMonadBaseIO___aux__3___redArg(v_a_26_, v_a_27_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__3___redArg___boxed(lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_instMonadBaseIO___aux__3___redArg(v_a_31_, v_a_32_);
lean_dec(v_a_31_);
return v_res_34_;
}
}
lean_object* l_instMonadBaseIO___aux__3(lean_object* v_00_u03b1_35_, lean_object* v_00_u03b2_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_apply_1(v_a_38_, lean_box(0));
lean_dec(v___x_40_);
lean_inc(v_a_37_);
return v_a_37_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_37_ = stack[2].m_obj;
lean_object* v_a_38_ = stack[3].m_obj;
lean_object* v_res_41_;
v_res_41_ = l_instMonadBaseIO___aux__3(lean_box(0), lean_box(0), v_a_37_, v_a_38_);
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__3___boxed(lean_object* v_00_u03b1_42_, lean_object* v_00_u03b2_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_instMonadBaseIO___aux__3(v_00_u03b1_42_, v_00_u03b2_43_, v_a_44_, v_a_45_);
lean_dec(v_a_44_);
return v_res_47_;
}
}
lean_object* l_instMonadBaseIO___aux__5___redArg(lean_object* v_x_48_){
_start:
{
lean_inc(v_x_48_);
return v_x_48_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_48_ = stack[0].m_obj;
lean_object* v_res_50_;
v_res_50_ = l_instMonadBaseIO___aux__5___redArg(v_x_48_);
stack->m_obj
 = v_res_50_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__5___redArg___boxed(lean_object* v_x_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_instMonadBaseIO___aux__5___redArg(v_x_51_);
lean_dec(v_x_51_);
return v_res_53_;
}
}
lean_object* l_instMonadBaseIO___aux__5(lean_object* v_00_u03b1_54_, lean_object* v_x_55_){
_start:
{
lean_inc(v_x_55_);
return v_x_55_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_55_ = stack[1].m_obj;
lean_object* v_res_57_;
v_res_57_ = l_instMonadBaseIO___aux__5(lean_box(0), v_x_55_);
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__5___boxed(lean_object* v_00_u03b1_58_, lean_object* v_x_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_instMonadBaseIO___aux__5(v_00_u03b1_58_, v_x_59_);
lean_dec(v_x_59_);
return v_res_61_;
}
}
lean_object* l_instMonadBaseIO___aux__7___redArg(lean_object* v_f_62_, lean_object* v_x_63_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = lean_apply_1(v_f_62_, lean_box(0));
v___x_66_ = lean_box(0);
v___x_67_ = lean_apply_2(v_x_63_, v___x_66_, lean_box(0));
v___x_68_ = lean_apply_1(v___x_65_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_62_ = stack[0].m_obj;
lean_object* v_x_63_ = stack[1].m_obj;
lean_object* v_res_69_;
v_res_69_ = l_instMonadBaseIO___aux__7___redArg(v_f_62_, v_x_63_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__7___redArg___boxed(lean_object* v_f_70_, lean_object* v_x_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_instMonadBaseIO___aux__7___redArg(v_f_70_, v_x_71_);
return v_res_73_;
}
}
lean_object* l_instMonadBaseIO___aux__7(lean_object* v_00_u03b1_74_, lean_object* v_00_u03b2_75_, lean_object* v_f_76_, lean_object* v_x_77_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_79_ = lean_apply_1(v_f_76_, lean_box(0));
v___x_80_ = lean_box(0);
v___x_81_ = lean_apply_2(v_x_77_, v___x_80_, lean_box(0));
v___x_82_ = lean_apply_1(v___x_79_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_76_ = stack[2].m_obj;
lean_object* v_x_77_ = stack[3].m_obj;
lean_object* v_res_83_;
v_res_83_ = l_instMonadBaseIO___aux__7(lean_box(0), lean_box(0), v_f_76_, v_x_77_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__7___boxed(lean_object* v_00_u03b1_84_, lean_object* v_00_u03b2_85_, lean_object* v_f_86_, lean_object* v_x_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_instMonadBaseIO___aux__7(v_00_u03b1_84_, v_00_u03b2_85_, v_f_86_, v_x_87_);
return v_res_89_;
}
}
lean_object* l_instMonadBaseIO___aux__9___redArg(lean_object* v_x_90_, lean_object* v_y_91_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_apply_1(v_x_90_, lean_box(0));
v___x_94_ = lean_box(0);
v___x_95_ = lean_apply_2(v_y_91_, v___x_94_, lean_box(0));
lean_dec(v___x_95_);
return v___x_93_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_90_ = stack[0].m_obj;
lean_object* v_y_91_ = stack[1].m_obj;
lean_object* v_res_96_;
v_res_96_ = l_instMonadBaseIO___aux__9___redArg(v_x_90_, v_y_91_);
stack->m_obj
 = v_res_96_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__9___redArg___boxed(lean_object* v_x_97_, lean_object* v_y_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_instMonadBaseIO___aux__9___redArg(v_x_97_, v_y_98_);
return v_res_100_;
}
}
lean_object* l_instMonadBaseIO___aux__9(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_x_103_, lean_object* v_y_104_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_apply_1(v_x_103_, lean_box(0));
v___x_107_ = lean_box(0);
v___x_108_ = lean_apply_2(v_y_104_, v___x_107_, lean_box(0));
lean_dec(v___x_108_);
return v___x_106_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_103_ = stack[2].m_obj;
lean_object* v_y_104_ = stack[3].m_obj;
lean_object* v_res_109_;
v_res_109_ = l_instMonadBaseIO___aux__9(lean_box(0), lean_box(0), v_x_103_, v_y_104_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__9___boxed(lean_object* v_00_u03b1_110_, lean_object* v_00_u03b2_111_, lean_object* v_x_112_, lean_object* v_y_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_instMonadBaseIO___aux__9(v_00_u03b1_110_, v_00_u03b2_111_, v_x_112_, v_y_113_);
return v_res_115_;
}
}
lean_object* l_instMonadBaseIO___aux__11___redArg(lean_object* v_x_116_, lean_object* v_y_117_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = lean_apply_1(v_x_116_, lean_box(0));
lean_dec(v___x_119_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_apply_2(v_y_117_, v___x_120_, lean_box(0));
return v___x_121_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_116_ = stack[0].m_obj;
lean_object* v_y_117_ = stack[1].m_obj;
lean_object* v_res_122_;
v_res_122_ = l_instMonadBaseIO___aux__11___redArg(v_x_116_, v_y_117_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__11___redArg___boxed(lean_object* v_x_123_, lean_object* v_y_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_instMonadBaseIO___aux__11___redArg(v_x_123_, v_y_124_);
return v_res_126_;
}
}
lean_object* l_instMonadBaseIO___aux__11(lean_object* v_00_u03b1_127_, lean_object* v_00_u03b2_128_, lean_object* v_x_129_, lean_object* v_y_130_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_apply_1(v_x_129_, lean_box(0));
lean_dec(v___x_132_);
v___x_133_ = lean_box(0);
v___x_134_ = lean_apply_2(v_y_130_, v___x_133_, lean_box(0));
return v___x_134_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_129_ = stack[2].m_obj;
lean_object* v_y_130_ = stack[3].m_obj;
lean_object* v_res_135_;
v_res_135_ = l_instMonadBaseIO___aux__11(lean_box(0), lean_box(0), v_x_129_, v_y_130_);
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__11___boxed(lean_object* v_00_u03b1_136_, lean_object* v_00_u03b2_137_, lean_object* v_x_138_, lean_object* v_y_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_instMonadBaseIO___aux__11(v_00_u03b1_136_, v_00_u03b2_137_, v_x_138_, v_y_139_);
return v_res_141_;
}
}
lean_object* l_instMonadBaseIO___aux__13___redArg(lean_object* v_x_142_, lean_object* v_f_143_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_apply_1(v_x_142_, lean_box(0));
v___x_146_ = lean_apply_2(v_f_143_, v___x_145_, lean_box(0));
return v___x_146_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_142_ = stack[0].m_obj;
lean_object* v_f_143_ = stack[1].m_obj;
lean_object* v_res_147_;
v_res_147_ = l_instMonadBaseIO___aux__13___redArg(v_x_142_, v_f_143_);
stack->m_obj
 = v_res_147_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__13___redArg___boxed(lean_object* v_x_148_, lean_object* v_f_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_instMonadBaseIO___aux__13___redArg(v_x_148_, v_f_149_);
return v_res_151_;
}
}
lean_object* l_instMonadBaseIO___aux__13(lean_object* v_00_u03b1_152_, lean_object* v_00_u03b2_153_, lean_object* v_x_154_, lean_object* v_f_155_){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_apply_1(v_x_154_, lean_box(0));
v___x_158_ = lean_apply_2(v_f_155_, v___x_157_, lean_box(0));
return v___x_158_;
}
}
LEAN_EXPORT void l_instMonadBaseIO___aux__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_154_ = stack[2].m_obj;
lean_object* v_f_155_ = stack[3].m_obj;
lean_object* v_res_159_;
v_res_159_ = l_instMonadBaseIO___aux__13(lean_box(0), lean_box(0), v_x_154_, v_f_155_);
stack->m_obj
 = v_res_159_;
}
LEAN_EXPORT lean_object* l_instMonadBaseIO___aux__13___boxed(lean_object* v_00_u03b1_160_, lean_object* v_00_u03b2_161_, lean_object* v_x_162_, lean_object* v_f_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_instMonadBaseIO___aux__13(v_00_u03b1_160_, v_00_u03b2_161_, v_x_162_, v_f_163_);
return v_res_165_;
}
}
lean_object* l_instMonadFinallyBaseIO___aux__1___redArg(lean_object* v_x_186_, lean_object* v_f_187_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = lean_apply_1(v_x_186_, lean_box(0));
lean_inc(v___x_189_);
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
v___x_191_ = lean_apply_2(v_f_187_, v___x_190_, lean_box(0));
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_189_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT void l_instMonadFinallyBaseIO___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_186_ = stack[0].m_obj;
lean_object* v_f_187_ = stack[1].m_obj;
lean_object* v_res_193_;
v_res_193_ = l_instMonadFinallyBaseIO___aux__1___redArg(v_x_186_, v_f_187_);
stack->m_obj
 = v_res_193_;
}
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO___aux__1___redArg___boxed(lean_object* v_x_194_, lean_object* v_f_195_, lean_object* v_s_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_instMonadFinallyBaseIO___aux__1___redArg(v_x_194_, v_f_195_);
return v_res_197_;
}
}
lean_object* l_instMonadFinallyBaseIO___aux__1(lean_object* v_00_u03b1_198_, lean_object* v_00_u03b2_199_, lean_object* v_x_200_, lean_object* v_f_201_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_203_ = lean_apply_1(v_x_200_, lean_box(0));
lean_inc(v___x_203_);
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
v___x_205_ = lean_apply_2(v_f_201_, v___x_204_, lean_box(0));
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_203_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT void l_instMonadFinallyBaseIO___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_200_ = stack[2].m_obj;
lean_object* v_f_201_ = stack[3].m_obj;
lean_object* v_res_207_;
v_res_207_ = l_instMonadFinallyBaseIO___aux__1(lean_box(0), lean_box(0), v_x_200_, v_f_201_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l_instMonadFinallyBaseIO___aux__1___boxed(lean_object* v_00_u03b1_208_, lean_object* v_00_u03b2_209_, lean_object* v_x_210_, lean_object* v_f_211_, lean_object* v_s_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_instMonadFinallyBaseIO___aux__1(v_00_u03b1_208_, v_00_u03b2_209_, v_x_210_, v_f_211_);
return v_res_213_;
}
}
lean_object* l_instMonadAttachBaseIO___aux__3___redArg(lean_object* v_x_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_apply_1(v_x_216_, lean_box(0));
return v___x_218_;
}
}
LEAN_EXPORT void l_instMonadAttachBaseIO___aux__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_216_ = stack[0].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_instMonadAttachBaseIO___aux__3___redArg(v_x_216_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_instMonadAttachBaseIO___aux__3___redArg___boxed(lean_object* v_x_220_, lean_object* v_s_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_instMonadAttachBaseIO___aux__3___redArg(v_x_220_);
return v_res_222_;
}
}
lean_object* l_instMonadAttachBaseIO___aux__3(lean_object* v_00_u03b1_223_, lean_object* v_x_224_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_apply_1(v_x_224_, lean_box(0));
return v___x_226_;
}
}
LEAN_EXPORT void l_instMonadAttachBaseIO___aux__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_224_ = stack[1].m_obj;
lean_object* v_res_227_;
v_res_227_ = l_instMonadAttachBaseIO___aux__3(lean_box(0), v_x_224_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l_instMonadAttachBaseIO___aux__3___boxed(lean_object* v_00_u03b1_228_, lean_object* v_x_229_, lean_object* v_s_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_instMonadAttachBaseIO___aux__3(v_00_u03b1_228_, v_x_229_);
return v_res_231_;
}
}
lean_object* l_BaseIO_map___redArg(lean_object* v_f_234_, lean_object* v_x_235_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_apply_1(v_x_235_, lean_box(0));
v___x_238_ = lean_apply_1(v_f_234_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT void l_BaseIO_map___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_234_ = stack[0].m_obj;
lean_object* v_x_235_ = stack[1].m_obj;
lean_object* v_res_239_;
v_res_239_ = l_BaseIO_map___redArg(v_f_234_, v_x_235_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l_BaseIO_map___redArg___boxed(lean_object* v_f_240_, lean_object* v_x_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_BaseIO_map___redArg(v_f_240_, v_x_241_);
return v_res_243_;
}
}
lean_object* l_BaseIO_map(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_f_246_, lean_object* v_x_247_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_apply_1(v_x_247_, lean_box(0));
v___x_250_ = lean_apply_1(v_f_246_, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT void l_BaseIO_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_246_ = stack[2].m_obj;
lean_object* v_x_247_ = stack[3].m_obj;
lean_object* v_res_251_;
v_res_251_ = l_BaseIO_map(lean_box(0), lean_box(0), v_f_246_, v_x_247_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l_BaseIO_map___boxed(lean_object* v_00_u03b1_252_, lean_object* v_00_u03b2_253_, lean_object* v_f_254_, lean_object* v_x_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_BaseIO_map(v_00_u03b1_252_, v_00_u03b2_253_, v_f_254_, v_x_255_);
return v_res_257_;
}
}
lean_object* l_BaseIO_toEIO___redArg(lean_object* v_act_258_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_apply_1(v_act_258_, lean_box(0));
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT void l_BaseIO_toEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_258_ = stack[0].m_obj;
lean_object* v_res_262_;
v_res_262_ = l_BaseIO_toEIO___redArg(v_act_258_);
stack->m_obj
 = v_res_262_;
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___redArg___boxed(lean_object* v_act_263_, lean_object* v_s_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_BaseIO_toEIO___redArg(v_act_263_);
return v_res_265_;
}
}
lean_object* l_BaseIO_toEIO(lean_object* v_00_u03b1_266_, lean_object* v_00_u03b5_267_, lean_object* v_act_268_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_apply_1(v_act_268_, lean_box(0));
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT void l_BaseIO_toEIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_268_ = stack[2].m_obj;
lean_object* v_res_272_;
v_res_272_ = l_BaseIO_toEIO(lean_box(0), lean_box(0), v_act_268_);
stack->m_obj
 = v_res_272_;
}
LEAN_EXPORT lean_object* l_BaseIO_toEIO___boxed(lean_object* v_00_u03b1_273_, lean_object* v_00_u03b5_274_, lean_object* v_act_275_, lean_object* v_s_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_BaseIO_toEIO(v_00_u03b1_273_, v_00_u03b5_274_, v_act_275_);
return v_res_277_;
}
}
lean_object* l_instMonadLiftBaseIOEIO___redArg___lam__0(lean_object* v_00_u03b1_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_apply_1(v___y_279_, lean_box(0));
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT void l_instMonadLiftBaseIOEIO___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_279_ = stack[1].m_obj;
lean_object* v_res_283_;
v_res_283_ = l_instMonadLiftBaseIOEIO___redArg___lam__0(lean_box(0), v___y_279_);
stack->m_obj
 = v_res_283_;
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___redArg___lam__0___boxed(lean_object* v_00_u03b1_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_instMonadLiftBaseIOEIO___redArg___lam__0(v_00_u03b1_284_, v___y_285_);
return v_res_287_;
}
}
lean_object* l_instMonadLiftBaseIOEIO___redArg(){
_start:
{
lean_object* v___f_290_; 
v___f_290_ = ((lean_object*)(l_instMonadLiftBaseIOEIO___redArg___closed__0));
return v___f_290_;
}
}
LEAN_EXPORT void l_instMonadLiftBaseIOEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_291_;
v_res_291_ = l_instMonadLiftBaseIOEIO___redArg();
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO___redArg___boxed(lean_object* v___dummy_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_instMonadLiftBaseIOEIO___redArg();
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_instMonadLiftBaseIOEIO(lean_object* v_00_u03b5_294_){
_start:
{
lean_object* v___f_295_; 
v___f_295_ = ((lean_object*)(l_instMonadLiftBaseIOEIO___redArg___closed__0));
return v___f_295_;
}
}
lean_object* l_EIO_toBaseIO___redArg(lean_object* v_act_296_){
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
LEAN_EXPORT void l_EIO_toBaseIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_296_ = stack[0].m_obj;
lean_object* v_res_315_;
v_res_315_ = l_EIO_toBaseIO___redArg(v_act_296_);
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___redArg___boxed(lean_object* v_act_316_, lean_object* v_s_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_EIO_toBaseIO___redArg(v_act_316_);
return v_res_318_;
}
}
lean_object* l_EIO_toBaseIO(lean_object* v_00_u03b5_319_, lean_object* v_00_u03b1_320_, lean_object* v_act_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_apply_1(v_act_321_, lean_box(0));
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set_tag(v___x_326_, 1);
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
v_a_332_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_323_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_323_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set_tag(v___x_334_, 0);
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_toBaseIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_321_ = stack[2].m_obj;
lean_object* v_res_340_;
v_res_340_ = l_EIO_toBaseIO(lean_box(0), lean_box(0), v_act_321_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l_EIO_toBaseIO___boxed(lean_object* v_00_u03b5_341_, lean_object* v_00_u03b1_342_, lean_object* v_act_343_, lean_object* v_s_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_EIO_toBaseIO(v_00_u03b5_341_, v_00_u03b1_342_, v_act_343_);
return v_res_345_;
}
}
lean_object* l_EIO_catchExceptions___redArg(lean_object* v_act_346_, lean_object* v_h_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_apply_1(v_act_346_, lean_box(0));
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; 
lean_dec_ref(v_h_347_);
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_349_, 1);
return v_a_350_;
}
else
{
lean_object* v_a_351_; lean_object* v___x_352_; 
v_a_351_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_349_, 1);
v___x_352_ = lean_apply_2(v_h_347_, v_a_351_, lean_box(0));
return v___x_352_;
}
}
}
LEAN_EXPORT void l_EIO_catchExceptions___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_346_ = stack[0].m_obj;
lean_object* v_h_347_ = stack[1].m_obj;
lean_object* v_res_353_;
v_res_353_ = l_EIO_catchExceptions___redArg(v_act_346_, v_h_347_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___redArg___boxed(lean_object* v_act_354_, lean_object* v_h_355_, lean_object* v_s_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_EIO_catchExceptions___redArg(v_act_354_, v_h_355_);
return v_res_357_;
}
}
lean_object* l_EIO_catchExceptions(lean_object* v_00_u03b5_358_, lean_object* v_00_u03b1_359_, lean_object* v_act_360_, lean_object* v_h_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_apply_1(v_act_360_, lean_box(0));
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; 
lean_dec_ref(v_h_361_);
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
return v_a_364_;
}
else
{
lean_object* v_a_365_; lean_object* v___x_366_; 
v_a_365_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_365_);
lean_dec_ref_known(v___x_363_, 1);
v___x_366_ = lean_apply_2(v_h_361_, v_a_365_, lean_box(0));
return v___x_366_;
}
}
}
LEAN_EXPORT void l_EIO_catchExceptions_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_360_ = stack[2].m_obj;
lean_object* v_h_361_ = stack[3].m_obj;
lean_object* v_res_367_;
v_res_367_ = l_EIO_catchExceptions(lean_box(0), lean_box(0), v_act_360_, v_h_361_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l_EIO_catchExceptions___boxed(lean_object* v_00_u03b5_368_, lean_object* v_00_u03b1_369_, lean_object* v_act_370_, lean_object* v_h_371_, lean_object* v_s_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_EIO_catchExceptions(v_00_u03b5_368_, v_00_u03b1_369_, v_act_370_, v_h_371_);
return v_res_373_;
}
}
lean_object* l_instMonadEIO___aux__1___redArg(lean_object* v_f_374_, lean_object* v_x_375_){
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
LEAN_EXPORT void l_instMonadEIO___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_374_ = stack[0].m_obj;
lean_object* v_x_375_ = stack[1].m_obj;
lean_object* v_res_395_;
v_res_395_ = l_instMonadEIO___aux__1___redArg(v_f_374_, v_x_375_);
stack->m_obj
 = v_res_395_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1___redArg___boxed(lean_object* v_f_396_, lean_object* v_x_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_instMonadEIO___aux__1___redArg(v_f_396_, v_x_397_);
return v_res_399_;
}
}
lean_object* l_instMonadEIO___aux__1(lean_object* v_00_u03b5_400_, lean_object* v_00_u03b1_401_, lean_object* v_00_u03b2_402_, lean_object* v_f_403_, lean_object* v_x_404_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lean_apply_1(v_x_404_, lean_box(0));
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_415_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_415_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = lean_apply_1(v_f_403_, v_a_407_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_f_403_);
v_a_416_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_406_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_406_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
LEAN_EXPORT void l_instMonadEIO___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_403_ = stack[3].m_obj;
lean_object* v_x_404_ = stack[4].m_obj;
lean_object* v_res_424_;
v_res_424_ = l_instMonadEIO___aux__1(lean_box(0), lean_box(0), lean_box(0), v_f_403_, v_x_404_);
stack->m_obj
 = v_res_424_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__1___boxed(lean_object* v_00_u03b5_425_, lean_object* v_00_u03b1_426_, lean_object* v_00_u03b2_427_, lean_object* v_f_428_, lean_object* v_x_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_instMonadEIO___aux__1(v_00_u03b5_425_, v_00_u03b1_426_, v_00_u03b2_427_, v_f_428_, v_x_429_);
return v_res_431_;
}
}
lean_object* l_instMonadEIO___aux__3___redArg(lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_apply_1(v_a_433_, lean_box(0));
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; 
v_unused_443_ = lean_ctor_get(v___x_435_, 0);
lean_dec(v_unused_443_);
v___x_437_ = v___x_435_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_dec(v___x_435_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v_a_432_);
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_432_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_dec(v_a_432_);
v_a_444_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_435_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_435_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT void l_instMonadEIO___aux__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_432_ = stack[0].m_obj;
lean_object* v_a_433_ = stack[1].m_obj;
lean_object* v_res_452_;
v_res_452_ = l_instMonadEIO___aux__3___redArg(v_a_432_, v_a_433_);
stack->m_obj
 = v_res_452_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3___redArg___boxed(lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_instMonadEIO___aux__3___redArg(v_a_453_, v_a_454_);
return v_res_456_;
}
}
lean_object* l_instMonadEIO___aux__3(lean_object* v_00_u03b5_457_, lean_object* v_00_u03b1_458_, lean_object* v_00_u03b2_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_apply_1(v_a_461_, lean_box(0));
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v___x_463_, 0);
lean_dec(v_unused_471_);
v___x_465_ = v___x_463_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_dec(v___x_463_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v_a_460_);
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_460_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec(v_a_460_);
v_a_472_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_463_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_463_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
LEAN_EXPORT void l_instMonadEIO___aux__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_460_ = stack[3].m_obj;
lean_object* v_a_461_ = stack[4].m_obj;
lean_object* v_res_480_;
v_res_480_ = l_instMonadEIO___aux__3(lean_box(0), lean_box(0), lean_box(0), v_a_460_, v_a_461_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__3___boxed(lean_object* v_00_u03b5_481_, lean_object* v_00_u03b1_482_, lean_object* v_00_u03b2_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_instMonadEIO___aux__3(v_00_u03b5_481_, v_00_u03b1_482_, v_00_u03b2_483_, v_a_484_, v_a_485_);
return v_res_487_;
}
}
lean_object* l_instMonadEIO___aux__5___redArg(lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v_a_488_);
return v___x_490_;
}
}
LEAN_EXPORT void l_instMonadEIO___aux__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_488_ = stack[0].m_obj;
lean_object* v_res_491_;
v_res_491_ = l_instMonadEIO___aux__5___redArg(v_a_488_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5___redArg___boxed(lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_instMonadEIO___aux__5___redArg(v_a_492_);
return v_res_494_;
}
}
lean_object* l_instMonadEIO___aux__5(lean_object* v_00_u03b5_495_, lean_object* v_00_u03b1_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v_a_497_);
return v___x_499_;
}
}
LEAN_EXPORT void l_instMonadEIO___aux__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_497_ = stack[2].m_obj;
lean_object* v_res_500_;
v_res_500_ = l_instMonadEIO___aux__5(lean_box(0), lean_box(0), v_a_497_);
stack->m_obj
 = v_res_500_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__5___boxed(lean_object* v_00_u03b5_501_, lean_object* v_00_u03b1_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_instMonadEIO___aux__5(v_00_u03b5_501_, v_00_u03b1_502_, v_a_503_);
return v_res_505_;
}
}
lean_object* l_instMonadEIO___aux__7___redArg(lean_object* v_f_506_, lean_object* v_x_507_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lean_apply_1(v_f_506_, lean_box(0));
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = lean_box(0);
v___x_512_ = lean_apply_2(v_x_507_, v___x_511_, lean_box(0));
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_521_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_521_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = lean_apply_1(v_a_510_, v_a_513_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_517_);
v___x_519_ = v___x_515_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_a_510_);
v_a_522_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_512_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_512_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec_ref(v_x_507_);
v_a_530_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_509_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_509_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
LEAN_EXPORT void l_instMonadEIO___aux__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_506_ = stack[0].m_obj;
lean_object* v_x_507_ = stack[1].m_obj;
lean_object* v_res_538_;
v_res_538_ = l_instMonadEIO___aux__7___redArg(v_f_506_, v_x_507_);
stack->m_obj
 = v_res_538_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7___redArg___boxed(lean_object* v_f_539_, lean_object* v_x_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_instMonadEIO___aux__7___redArg(v_f_539_, v_x_540_);
return v_res_542_;
}
}
lean_object* l_instMonadEIO___aux__7(lean_object* v_00_u03b5_543_, lean_object* v_00_u03b1_544_, lean_object* v_00_u03b2_545_, lean_object* v_f_546_, lean_object* v_x_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = lean_apply_1(v_f_546_, lean_box(0));
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_549_, 1);
v___x_551_ = lean_box(0);
v___x_552_ = lean_apply_2(v_x_547_, v___x_551_, lean_box(0));
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_561_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_561_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_561_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_561_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = lean_apply_1(v_a_550_, v_a_553_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_557_);
v___x_559_ = v___x_555_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_a_550_);
v_a_562_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_552_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_552_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
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
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v_x_547_);
v_a_570_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_549_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_549_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT void l_instMonadEIO___aux__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_546_ = stack[3].m_obj;
lean_object* v_x_547_ = stack[4].m_obj;
lean_object* v_res_578_;
v_res_578_ = l_instMonadEIO___aux__7(lean_box(0), lean_box(0), lean_box(0), v_f_546_, v_x_547_);
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__7___boxed(lean_object* v_00_u03b5_579_, lean_object* v_00_u03b1_580_, lean_object* v_00_u03b2_581_, lean_object* v_f_582_, lean_object* v_x_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_instMonadEIO___aux__7(v_00_u03b5_579_, v_00_u03b1_580_, v_00_u03b2_581_, v_f_582_, v_x_583_);
return v_res_585_;
}
}
lean_object* l_instMonadEIO___aux__9___redArg(lean_object* v_x_586_, lean_object* v_y_587_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_apply_1(v_x_586_, lean_box(0));
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
v___x_591_ = lean_box(0);
v___x_592_ = lean_apply_2(v_y_587_, v___x_591_, lean_box(0));
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v___x_592_, 0);
lean_dec(v_unused_600_);
v___x_594_ = v___x_592_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_dec(v___x_592_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v_a_590_);
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_590_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec(v_a_590_);
v_a_601_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_592_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_592_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
else
{
lean_dec_ref(v_y_587_);
return v___x_589_;
}
}
}
LEAN_EXPORT void l_instMonadEIO___aux__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_586_ = stack[0].m_obj;
lean_object* v_y_587_ = stack[1].m_obj;
lean_object* v_res_609_;
v_res_609_ = l_instMonadEIO___aux__9___redArg(v_x_586_, v_y_587_);
stack->m_obj
 = v_res_609_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9___redArg___boxed(lean_object* v_x_610_, lean_object* v_y_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_instMonadEIO___aux__9___redArg(v_x_610_, v_y_611_);
return v_res_613_;
}
}
lean_object* l_instMonadEIO___aux__9(lean_object* v_00_u03b5_614_, lean_object* v_00_u03b1_615_, lean_object* v_00_u03b2_616_, lean_object* v_x_617_, lean_object* v_y_618_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lean_apply_1(v_x_617_, lean_box(0));
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v___x_622_ = lean_box(0);
v___x_623_ = lean_apply_2(v_y_618_, v___x_622_, lean_box(0));
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v___x_623_, 0);
lean_dec(v_unused_631_);
v___x_625_ = v___x_623_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_dec(v___x_623_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v_a_621_);
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_621_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v_a_621_);
v_a_632_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_623_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_623_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_dec_ref(v_y_618_);
return v___x_620_;
}
}
}
LEAN_EXPORT void l_instMonadEIO___aux__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_617_ = stack[3].m_obj;
lean_object* v_y_618_ = stack[4].m_obj;
lean_object* v_res_640_;
v_res_640_ = l_instMonadEIO___aux__9(lean_box(0), lean_box(0), lean_box(0), v_x_617_, v_y_618_);
stack->m_obj
 = v_res_640_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__9___boxed(lean_object* v_00_u03b5_641_, lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_x_644_, lean_object* v_y_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_instMonadEIO___aux__9(v_00_u03b5_641_, v_00_u03b1_642_, v_00_u03b2_643_, v_x_644_, v_y_645_);
return v_res_647_;
}
}
lean_object* l_instMonadEIO___aux__11___redArg(lean_object* v_x_648_, lean_object* v_y_649_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = lean_apply_1(v_x_648_, lean_box(0));
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec_ref_known(v___x_651_, 1);
v___x_652_ = lean_box(0);
v___x_653_ = lean_apply_2(v_y_649_, v___x_652_, lean_box(0));
return v___x_653_;
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v_y_649_);
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
LEAN_EXPORT void l_instMonadEIO___aux__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_648_ = stack[0].m_obj;
lean_object* v_y_649_ = stack[1].m_obj;
lean_object* v_res_662_;
v_res_662_ = l_instMonadEIO___aux__11___redArg(v_x_648_, v_y_649_);
stack->m_obj
 = v_res_662_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11___redArg___boxed(lean_object* v_x_663_, lean_object* v_y_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_instMonadEIO___aux__11___redArg(v_x_663_, v_y_664_);
return v_res_666_;
}
}
lean_object* l_instMonadEIO___aux__11(lean_object* v_00_u03b5_667_, lean_object* v_00_u03b1_668_, lean_object* v_00_u03b2_669_, lean_object* v_x_670_, lean_object* v_y_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = lean_apply_1(v_x_670_, lean_box(0));
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; 
lean_dec_ref_known(v___x_673_, 1);
v___x_674_ = lean_box(0);
v___x_675_ = lean_apply_2(v_y_671_, v___x_674_, lean_box(0));
return v___x_675_;
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v_y_671_);
v_a_676_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_673_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_673_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
LEAN_EXPORT void l_instMonadEIO___aux__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_670_ = stack[3].m_obj;
lean_object* v_y_671_ = stack[4].m_obj;
lean_object* v_res_684_;
v_res_684_ = l_instMonadEIO___aux__11(lean_box(0), lean_box(0), lean_box(0), v_x_670_, v_y_671_);
stack->m_obj
 = v_res_684_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__11___boxed(lean_object* v_00_u03b5_685_, lean_object* v_00_u03b1_686_, lean_object* v_00_u03b2_687_, lean_object* v_x_688_, lean_object* v_y_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_instMonadEIO___aux__11(v_00_u03b5_685_, v_00_u03b1_686_, v_00_u03b2_687_, v_x_688_, v_y_689_);
return v_res_691_;
}
}
lean_object* l_instMonadEIO___aux__13___redArg(lean_object* v_x_692_, lean_object* v_f_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = lean_apply_1(v_x_692_, lean_box(0));
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_697_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
v___x_697_ = lean_apply_2(v_f_693_, v_a_696_, lean_box(0));
return v___x_697_;
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref(v_f_693_);
v_a_698_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_695_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_695_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
LEAN_EXPORT void l_instMonadEIO___aux__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_692_ = stack[0].m_obj;
lean_object* v_f_693_ = stack[1].m_obj;
lean_object* v_res_706_;
v_res_706_ = l_instMonadEIO___aux__13___redArg(v_x_692_, v_f_693_);
stack->m_obj
 = v_res_706_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13___redArg___boxed(lean_object* v_x_707_, lean_object* v_f_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_instMonadEIO___aux__13___redArg(v_x_707_, v_f_708_);
return v_res_710_;
}
}
lean_object* l_instMonadEIO___aux__13(lean_object* v_00_u03b5_711_, lean_object* v_00_u03b1_712_, lean_object* v_00_u03b2_713_, lean_object* v_x_714_, lean_object* v_f_715_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_apply_1(v_x_714_, lean_box(0));
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_719_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v___x_719_ = lean_apply_2(v_f_715_, v_a_718_, lean_box(0));
return v___x_719_;
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref(v_f_715_);
v_a_720_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_717_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_717_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
LEAN_EXPORT void l_instMonadEIO___aux__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_714_ = stack[3].m_obj;
lean_object* v_f_715_ = stack[4].m_obj;
lean_object* v_res_728_;
v_res_728_ = l_instMonadEIO___aux__13(lean_box(0), lean_box(0), lean_box(0), v_x_714_, v_f_715_);
stack->m_obj
 = v_res_728_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___aux__13___boxed(lean_object* v_00_u03b5_729_, lean_object* v_00_u03b1_730_, lean_object* v_00_u03b2_731_, lean_object* v_x_732_, lean_object* v_f_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_instMonadEIO___aux__13(v_00_u03b5_729_, v_00_u03b1_730_, v_00_u03b2_731_, v_x_732_, v_f_733_);
return v_res_735_;
}
}
lean_object* l_instMonadEIO___redArg(){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = ((lean_object*)(l_instMonadEIO___redArg___closed__9));
return v___x_756_;
}
}
LEAN_EXPORT void l_instMonadEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_757_;
v_res_757_ = l_instMonadEIO___redArg();
stack->m_obj
 = v_res_757_;
}
LEAN_EXPORT lean_object* l_instMonadEIO___redArg___boxed(lean_object* v___dummy_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_instMonadEIO___redArg();
return v_res_759_;
}
}
static lean_object* _init_l_instMonadEIO___closed__0(void){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_instMonadEIO___redArg();
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_instMonadEIO(lean_object* v_00_u03b5_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = lean_obj_once(&l_instMonadEIO___closed__0, &l_instMonadEIO___closed__0_once, _init_l_instMonadEIO___closed__0);
return v___x_762_;
}
}
lean_object* l_instMonadFinallyEIO___aux__1___redArg(lean_object* v_x_763_, lean_object* v_f_764_){
_start:
{
lean_object* v_r_766_; 
v_r_766_ = lean_apply_1(v_x_763_, lean_box(0));
if (lean_obj_tag(v_r_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_792_; 
v_a_767_ = lean_ctor_get(v_r_766_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v_r_766_);
if (v_isSharedCheck_792_ == 0)
{
v___x_769_ = v_r_766_;
v_isShared_770_ = v_isSharedCheck_792_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v_r_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_792_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
lean_inc(v_a_767_);
if (v_isShared_770_ == 0)
{
lean_ctor_set_tag(v___x_769_, 1);
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_791_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; 
v___x_773_ = lean_apply_2(v_f_764_, v___x_772_, lean_box(0));
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_782_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v_a_767_);
lean_ctor_set(v___x_778_, 1, v_a_774_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_a_767_);
v_a_783_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_773_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_773_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_a_793_ = lean_ctor_get(v_r_766_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v_r_766_, 1);
v___x_794_ = lean_box(0);
v___x_795_ = lean_apply_2(v_f_764_, v___x_794_, lean_box(0));
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v___x_795_, 0);
lean_dec(v_unused_803_);
v___x_797_ = v___x_795_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_dec(v___x_795_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set_tag(v___x_797_, 1);
lean_ctor_set(v___x_797_, 0, v_a_793_);
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_793_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_a_793_);
v_a_804_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_795_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_795_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
}
LEAN_EXPORT void l_instMonadFinallyEIO___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_763_ = stack[0].m_obj;
lean_object* v_f_764_ = stack[1].m_obj;
lean_object* v_res_812_;
v_res_812_ = l_instMonadFinallyEIO___aux__1___redArg(v_x_763_, v_f_764_);
stack->m_obj
 = v_res_812_;
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___redArg___boxed(lean_object* v_x_813_, lean_object* v_f_814_, lean_object* v_s_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_instMonadFinallyEIO___aux__1___redArg(v_x_813_, v_f_814_);
return v_res_816_;
}
}
lean_object* l_instMonadFinallyEIO___aux__1(lean_object* v_00_u03b5_817_, lean_object* v_00_u03b1_818_, lean_object* v_00_u03b2_819_, lean_object* v_x_820_, lean_object* v_f_821_){
_start:
{
lean_object* v_r_823_; 
v_r_823_ = lean_apply_1(v_x_820_, lean_box(0));
if (lean_obj_tag(v_r_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_849_; 
v_a_824_ = lean_ctor_get(v_r_823_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v_r_823_);
if (v_isSharedCheck_849_ == 0)
{
v___x_826_ = v_r_823_;
v_isShared_827_ = v_isSharedCheck_849_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v_r_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_849_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
lean_inc(v_a_824_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 1);
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_848_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; 
v___x_830_ = lean_apply_2(v_f_821_, v___x_829_, lean_box(0));
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_839_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_839_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_a_824_);
lean_ctor_set(v___x_835_, 1, v_a_831_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_835_);
v___x_837_ = v___x_833_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_a_824_);
v_a_840_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_830_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_830_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_a_850_ = lean_ctor_get(v_r_823_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v_r_823_, 1);
v___x_851_ = lean_box(0);
v___x_852_ = lean_apply_2(v_f_821_, v___x_851_, lean_box(0));
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; 
v_unused_860_ = lean_ctor_get(v___x_852_, 0);
lean_dec(v_unused_860_);
v___x_854_ = v___x_852_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_dec(v___x_852_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 1);
lean_ctor_set(v___x_854_, 0, v_a_850_);
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_850_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_a_850_);
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
}
LEAN_EXPORT void l_instMonadFinallyEIO___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_820_ = stack[3].m_obj;
lean_object* v_f_821_ = stack[4].m_obj;
lean_object* v_res_869_;
v_res_869_ = l_instMonadFinallyEIO___aux__1(lean_box(0), lean_box(0), lean_box(0), v_x_820_, v_f_821_);
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___aux__1___boxed(lean_object* v_00_u03b5_870_, lean_object* v_00_u03b1_871_, lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_f_874_, lean_object* v_s_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_instMonadFinallyEIO___aux__1(v_00_u03b5_870_, v_00_u03b1_871_, v_00_u03b2_872_, v_x_873_, v_f_874_);
return v_res_876_;
}
}
lean_object* l_instMonadFinallyEIO___redArg(){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = ((lean_object*)(l_instMonadFinallyEIO___redArg___closed__0));
return v___x_879_;
}
}
LEAN_EXPORT void l_instMonadFinallyEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_880_;
v_res_880_ = l_instMonadFinallyEIO___redArg();
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO___redArg___boxed(lean_object* v___dummy_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_instMonadFinallyEIO___redArg();
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_instMonadFinallyEIO(lean_object* v_00_u03b5_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = ((lean_object*)(l_instMonadFinallyEIO___redArg___closed__0));
return v___x_884_;
}
}
lean_object* l_instMonadAttachEIO___aux__3___redArg(lean_object* v_x_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_apply_1(v_x_885_, lean_box(0));
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
v_a_896_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_887_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_887_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT void l_instMonadAttachEIO___aux__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_885_ = stack[0].m_obj;
lean_object* v_res_904_;
v_res_904_ = l_instMonadAttachEIO___aux__3___redArg(v_x_885_);
stack->m_obj
 = v_res_904_;
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___redArg___boxed(lean_object* v_x_905_, lean_object* v_s_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_instMonadAttachEIO___aux__3___redArg(v_x_905_);
return v_res_907_;
}
}
lean_object* l_instMonadAttachEIO___aux__3(lean_object* v_00_u03b5_908_, lean_object* v_00_u03b1_909_, lean_object* v_x_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_apply_1(v_x_910_, lean_box(0));
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
v_a_921_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_912_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_912_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
LEAN_EXPORT void l_instMonadAttachEIO___aux__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_910_ = stack[2].m_obj;
lean_object* v_res_929_;
v_res_929_ = l_instMonadAttachEIO___aux__3(lean_box(0), lean_box(0), v_x_910_);
stack->m_obj
 = v_res_929_;
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO___aux__3___boxed(lean_object* v_00_u03b5_930_, lean_object* v_00_u03b1_931_, lean_object* v_x_932_, lean_object* v_s_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_instMonadAttachEIO___aux__3(v_00_u03b5_930_, v_00_u03b1_931_, v_x_932_);
return v_res_934_;
}
}
lean_object* l_instMonadAttachEIO___redArg(){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = ((lean_object*)(l_instMonadAttachEIO___redArg___closed__0));
return v___x_937_;
}
}
LEAN_EXPORT void l_instMonadAttachEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_938_;
v_res_938_ = l_instMonadAttachEIO___redArg();
stack->m_obj
 = v_res_938_;
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO___redArg___boxed(lean_object* v___dummy_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_instMonadAttachEIO___redArg();
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_instMonadAttachEIO(lean_object* v_00_u03b5_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = ((lean_object*)(l_instMonadAttachEIO___redArg___closed__0));
return v___x_942_;
}
}
lean_object* l_instMonadExceptOfEIO___aux__1___redArg(lean_object* v_e_943_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_945_, 0, v_e_943_);
return v___x_945_;
}
}
LEAN_EXPORT void l_instMonadExceptOfEIO___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_943_ = stack[0].m_obj;
lean_object* v_res_946_;
v_res_946_ = l_instMonadExceptOfEIO___aux__1___redArg(v_e_943_);
stack->m_obj
 = v_res_946_;
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___redArg___boxed(lean_object* v_e_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_instMonadExceptOfEIO___aux__1___redArg(v_e_947_);
return v_res_949_;
}
}
lean_object* l_instMonadExceptOfEIO___aux__1(lean_object* v_00_u03b5_950_, lean_object* v_00_u03b1_951_, lean_object* v_e_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_954_, 0, v_e_952_);
return v___x_954_;
}
}
LEAN_EXPORT void l_instMonadExceptOfEIO___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_952_ = stack[2].m_obj;
lean_object* v_res_955_;
v_res_955_ = l_instMonadExceptOfEIO___aux__1(lean_box(0), lean_box(0), v_e_952_);
stack->m_obj
 = v_res_955_;
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__1___boxed(lean_object* v_00_u03b5_956_, lean_object* v_00_u03b1_957_, lean_object* v_e_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_instMonadExceptOfEIO___aux__1(v_00_u03b5_956_, v_00_u03b1_957_, v_e_958_);
return v_res_960_;
}
}
lean_object* l_instMonadExceptOfEIO___aux__3___redArg(lean_object* v_x_961_, lean_object* v_handle_962_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = lean_apply_1(v_x_961_, lean_box(0));
if (lean_obj_tag(v___x_964_) == 0)
{
lean_dec_ref(v_handle_962_);
return v___x_964_;
}
else
{
lean_object* v_a_965_; lean_object* v___x_966_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = lean_apply_2(v_handle_962_, v_a_965_, lean_box(0));
return v___x_966_;
}
}
}
LEAN_EXPORT void l_instMonadExceptOfEIO___aux__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_961_ = stack[0].m_obj;
lean_object* v_handle_962_ = stack[1].m_obj;
lean_object* v_res_967_;
v_res_967_ = l_instMonadExceptOfEIO___aux__3___redArg(v_x_961_, v_handle_962_);
stack->m_obj
 = v_res_967_;
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___redArg___boxed(lean_object* v_x_968_, lean_object* v_handle_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_instMonadExceptOfEIO___aux__3___redArg(v_x_968_, v_handle_969_);
return v_res_971_;
}
}
lean_object* l_instMonadExceptOfEIO___aux__3(lean_object* v_00_u03b5_972_, lean_object* v_00_u03b1_973_, lean_object* v_x_974_, lean_object* v_handle_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = lean_apply_1(v_x_974_, lean_box(0));
if (lean_obj_tag(v___x_977_) == 0)
{
lean_dec_ref(v_handle_975_);
return v___x_977_;
}
else
{
lean_object* v_a_978_; lean_object* v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = lean_apply_2(v_handle_975_, v_a_978_, lean_box(0));
return v___x_979_;
}
}
}
LEAN_EXPORT void l_instMonadExceptOfEIO___aux__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_974_ = stack[2].m_obj;
lean_object* v_handle_975_ = stack[3].m_obj;
lean_object* v_res_980_;
v_res_980_ = l_instMonadExceptOfEIO___aux__3(lean_box(0), lean_box(0), v_x_974_, v_handle_975_);
stack->m_obj
 = v_res_980_;
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___aux__3___boxed(lean_object* v_00_u03b5_981_, lean_object* v_00_u03b1_982_, lean_object* v_x_983_, lean_object* v_handle_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_instMonadExceptOfEIO___aux__3(v_00_u03b5_981_, v_00_u03b1_982_, v_x_983_, v_handle_984_);
return v_res_986_;
}
}
lean_object* l_instMonadExceptOfEIO___redArg(){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = ((lean_object*)(l_instMonadExceptOfEIO___redArg___closed__2));
return v___x_993_;
}
}
LEAN_EXPORT void l_instMonadExceptOfEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_994_;
v_res_994_ = l_instMonadExceptOfEIO___redArg();
stack->m_obj
 = v_res_994_;
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO___redArg___boxed(lean_object* v___dummy_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_instMonadExceptOfEIO___redArg();
return v_res_996_;
}
}
static lean_object* _init_l_instMonadExceptOfEIO___closed__0(void){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_instMonadExceptOfEIO___redArg();
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_instMonadExceptOfEIO(lean_object* v_00_u03b5_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = lean_obj_once(&l_instMonadExceptOfEIO___closed__0, &l_instMonadExceptOfEIO___closed__0_once, _init_l_instMonadExceptOfEIO___closed__0);
return v___x_999_;
}
}
static lean_object* _init_l_instOrElseEIO___redArg___closed__0(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_obj_once(&l_instMonadExceptOfEIO___closed__0, &l_instMonadExceptOfEIO___closed__0_once, _init_l_instMonadExceptOfEIO___closed__0);
v___x_1001_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_instOrElseEIO___redArg___closed__1(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_obj_once(&l_instOrElseEIO___redArg___closed__0, &l_instOrElseEIO___redArg___closed__0_once, _init_l_instOrElseEIO___redArg___closed__0);
v___x_1003_ = lean_alloc_closure((void*)(l_MonadExcept_orElse), 6, 4);
lean_closure_set(v___x_1003_, 0, lean_box(0));
lean_closure_set(v___x_1003_, 1, lean_box(0));
lean_closure_set(v___x_1003_, 2, v___x_1002_);
lean_closure_set(v___x_1003_, 3, lean_box(0));
return v___x_1003_;
}
}
lean_object* l_instOrElseEIO___redArg(){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_obj_once(&l_instOrElseEIO___redArg___closed__1, &l_instOrElseEIO___redArg___closed__1_once, _init_l_instOrElseEIO___redArg___closed__1);
return v___x_1005_;
}
}
LEAN_EXPORT void l_instOrElseEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1006_;
v_res_1006_ = l_instOrElseEIO___redArg();
stack->m_obj
 = v_res_1006_;
}
LEAN_EXPORT lean_object* l_instOrElseEIO___redArg___boxed(lean_object* v___dummy_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_instOrElseEIO___redArg();
return v_res_1008_;
}
}
static lean_object* _init_l_instOrElseEIO___closed__0(void){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_instOrElseEIO___redArg();
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_instOrElseEIO(lean_object* v_00_u03b5_1010_, lean_object* v_00_u03b1_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_obj_once(&l_instOrElseEIO___closed__0, &l_instOrElseEIO___closed__0_once, _init_l_instOrElseEIO___closed__0);
return v___x_1012_;
}
}
lean_object* l_instInhabitedEIO___aux__1___redArg(lean_object* v_inst_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_inst_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT void l_instInhabitedEIO___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1013_ = stack[0].m_obj;
lean_object* v_res_1016_;
v_res_1016_ = l_instInhabitedEIO___aux__1___redArg(v_inst_1013_);
stack->m_obj
 = v_res_1016_;
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1___redArg___boxed(lean_object* v_inst_1017_, lean_object* v_s_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_instInhabitedEIO___aux__1___redArg(v_inst_1017_);
return v_res_1019_;
}
}
lean_object* l_instInhabitedEIO___aux__1(lean_object* v_00_u03b5_1020_, lean_object* v_00_u03b1_1021_, lean_object* v_inst_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v_inst_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT void l_instInhabitedEIO___aux__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1022_ = stack[2].m_obj;
lean_object* v_res_1025_;
v_res_1025_ = l_instInhabitedEIO___aux__1(lean_box(0), lean_box(0), v_inst_1022_);
stack->m_obj
 = v_res_1025_;
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object* v_00_u03b5_1026_, lean_object* v_00_u03b1_1027_, lean_object* v_inst_1028_, lean_object* v_s_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_instInhabitedEIO___aux__1(v_00_u03b5_1026_, v_00_u03b1_1027_, v_inst_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO___redArg(lean_object* v_inst_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_1032_, 0, lean_box(0));
lean_closure_set(v___x_1032_, 1, lean_box(0));
lean_closure_set(v___x_1032_, 2, v_inst_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_instInhabitedEIO(lean_object* v_00_u03b5_1033_, lean_object* v_00_u03b1_1034_, lean_object* v_inst_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_1036_, 0, lean_box(0));
lean_closure_set(v___x_1036_, 1, lean_box(0));
lean_closure_set(v___x_1036_, 2, v_inst_1035_);
return v___x_1036_;
}
}
lean_object* l_EIO_map___redArg(lean_object* v_f_1037_, lean_object* v_x_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_apply_1(v_x_1038_, lean_box(0));
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1049_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = lean_apply_1(v_f_1037_, v_a_1041_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1045_);
v___x_1047_ = v___x_1043_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_f_1037_);
v_a_1050_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1040_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1040_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_map___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1037_ = stack[0].m_obj;
lean_object* v_x_1038_ = stack[1].m_obj;
lean_object* v_res_1058_;
v_res_1058_ = l_EIO_map___redArg(v_f_1037_, v_x_1038_);
stack->m_obj
 = v_res_1058_;
}
LEAN_EXPORT lean_object* l_EIO_map___redArg___boxed(lean_object* v_f_1059_, lean_object* v_x_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_EIO_map___redArg(v_f_1059_, v_x_1060_);
return v_res_1062_;
}
}
lean_object* l_EIO_map(lean_object* v_00_u03b1_1063_, lean_object* v_00_u03b2_1064_, lean_object* v_00_u03b5_1065_, lean_object* v_f_1066_, lean_object* v_x_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_apply_1(v_x_1067_, lean_box(0));
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1078_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_apply_1(v_f_1066_, v_a_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1074_);
v___x_1076_ = v___x_1072_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec(v_f_1066_);
v_a_1079_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1069_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1069_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1066_ = stack[3].m_obj;
lean_object* v_x_1067_ = stack[4].m_obj;
lean_object* v_res_1087_;
v_res_1087_ = l_EIO_map(lean_box(0), lean_box(0), lean_box(0), v_f_1066_, v_x_1067_);
stack->m_obj
 = v_res_1087_;
}
LEAN_EXPORT lean_object* l_EIO_map___boxed(lean_object* v_00_u03b1_1088_, lean_object* v_00_u03b2_1089_, lean_object* v_00_u03b5_1090_, lean_object* v_f_1091_, lean_object* v_x_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_EIO_map(v_00_u03b1_1088_, v_00_u03b2_1089_, v_00_u03b5_1090_, v_f_1091_, v_x_1092_);
return v_res_1094_;
}
}
lean_object* l_EIO_throw___redArg(lean_object* v_e_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_e_1095_);
return v___x_1097_;
}
}
LEAN_EXPORT void l_EIO_throw___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1095_ = stack[0].m_obj;
lean_object* v_res_1098_;
v_res_1098_ = l_EIO_throw___redArg(v_e_1095_);
stack->m_obj
 = v_res_1098_;
}
LEAN_EXPORT lean_object* l_EIO_throw___redArg___boxed(lean_object* v_e_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_EIO_throw___redArg(v_e_1099_);
return v_res_1101_;
}
}
lean_object* l_EIO_throw(lean_object* v_00_u03b5_1102_, lean_object* v_00_u03b1_1103_, lean_object* v_e_1104_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_e_1104_);
return v___x_1106_;
}
}
LEAN_EXPORT void l_EIO_throw_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1104_ = stack[2].m_obj;
lean_object* v_res_1107_;
v_res_1107_ = l_EIO_throw(lean_box(0), lean_box(0), v_e_1104_);
stack->m_obj
 = v_res_1107_;
}
LEAN_EXPORT lean_object* l_EIO_throw___boxed(lean_object* v_00_u03b5_1108_, lean_object* v_00_u03b1_1109_, lean_object* v_e_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_EIO_throw(v_00_u03b5_1108_, v_00_u03b1_1109_, v_e_1110_);
return v_res_1112_;
}
}
lean_object* l_EIO_tryCatch___redArg(lean_object* v_x_1113_, lean_object* v_handle_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_apply_1(v_x_1113_, lean_box(0));
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_dec_ref(v_handle_1114_);
return v___x_1116_;
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1118_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = lean_apply_2(v_handle_1114_, v_a_1117_, lean_box(0));
return v___x_1118_;
}
}
}
LEAN_EXPORT void l_EIO_tryCatch___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1113_ = stack[0].m_obj;
lean_object* v_handle_1114_ = stack[1].m_obj;
lean_object* v_res_1119_;
v_res_1119_ = l_EIO_tryCatch___redArg(v_x_1113_, v_handle_1114_);
stack->m_obj
 = v_res_1119_;
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___redArg___boxed(lean_object* v_x_1120_, lean_object* v_handle_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_EIO_tryCatch___redArg(v_x_1120_, v_handle_1121_);
return v_res_1123_;
}
}
lean_object* l_EIO_tryCatch(lean_object* v_00_u03b5_1124_, lean_object* v_00_u03b1_1125_, lean_object* v_x_1126_, lean_object* v_handle_1127_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_apply_1(v_x_1126_, lean_box(0));
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_dec_ref(v_handle_1127_);
return v___x_1129_;
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1131_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v___x_1131_ = lean_apply_2(v_handle_1127_, v_a_1130_, lean_box(0));
return v___x_1131_;
}
}
}
LEAN_EXPORT void l_EIO_tryCatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1126_ = stack[2].m_obj;
lean_object* v_handle_1127_ = stack[3].m_obj;
lean_object* v_res_1132_;
v_res_1132_ = l_EIO_tryCatch(lean_box(0), lean_box(0), v_x_1126_, v_handle_1127_);
stack->m_obj
 = v_res_1132_;
}
LEAN_EXPORT lean_object* l_EIO_tryCatch___boxed(lean_object* v_00_u03b5_1133_, lean_object* v_00_u03b1_1134_, lean_object* v_x_1135_, lean_object* v_handle_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_EIO_tryCatch(v_00_u03b5_1133_, v_00_u03b1_1134_, v_x_1135_, v_handle_1136_);
return v_res_1138_;
}
}
lean_object* l_EIO_ofExcept___redArg(lean_object* v_e_1139_){
_start:
{
if (lean_obj_tag(v_e_1139_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_a_1141_ = lean_ctor_get(v_e_1139_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_e_1139_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v_e_1139_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v_e_1139_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 1);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
v_a_1149_ = lean_ctor_get(v_e_1139_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_e_1139_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v_e_1139_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v_e_1139_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 0);
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_ofExcept___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1139_ = stack[0].m_obj;
lean_object* v_res_1157_;
v_res_1157_ = l_EIO_ofExcept___redArg(v_e_1139_);
stack->m_obj
 = v_res_1157_;
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___redArg___boxed(lean_object* v_e_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_EIO_ofExcept___redArg(v_e_1158_);
return v_res_1160_;
}
}
lean_object* l_EIO_ofExcept(lean_object* v_00_u03b5_1161_, lean_object* v_00_u03b1_1162_, lean_object* v_e_1163_){
_start:
{
if (lean_obj_tag(v_e_1163_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_a_1165_ = lean_ctor_get(v_e_1163_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_e_1163_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v_e_1163_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v_e_1163_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set_tag(v___x_1167_, 1);
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
v_a_1173_ = lean_ctor_get(v_e_1163_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_e_1163_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v_e_1163_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v_e_1163_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set_tag(v___x_1175_, 0);
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_ofExcept_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1163_ = stack[2].m_obj;
lean_object* v_res_1181_;
v_res_1181_ = l_EIO_ofExcept(lean_box(0), lean_box(0), v_e_1163_);
stack->m_obj
 = v_res_1181_;
}
LEAN_EXPORT lean_object* l_EIO_ofExcept___boxed(lean_object* v_00_u03b5_1182_, lean_object* v_00_u03b1_1183_, lean_object* v_e_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_EIO_ofExcept(v_00_u03b5_1182_, v_00_u03b1_1183_, v_e_1184_);
return v_res_1186_;
}
}
lean_object* l_EIO_adapt___redArg(lean_object* v_f_1187_, lean_object* v_m_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_apply_1(v_m_1188_, lean_box(0));
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec(v_f_1187_);
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1207_; 
v_a_1199_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1201_ = v___x_1190_;
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1190_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_apply_1(v_f_1187_, v_a_1199_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1203_);
v___x_1205_ = v___x_1201_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_adapt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1187_ = stack[0].m_obj;
lean_object* v_m_1188_ = stack[1].m_obj;
lean_object* v_res_1208_;
v_res_1208_ = l_EIO_adapt___redArg(v_f_1187_, v_m_1188_);
stack->m_obj
 = v_res_1208_;
}
LEAN_EXPORT lean_object* l_EIO_adapt___redArg___boxed(lean_object* v_f_1209_, lean_object* v_m_1210_, lean_object* v_s_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_EIO_adapt___redArg(v_f_1209_, v_m_1210_);
return v_res_1212_;
}
}
lean_object* l_EIO_adapt(lean_object* v_00_u03b5_1213_, lean_object* v_00_u03b5_x27_1214_, lean_object* v_00_u03b1_1215_, lean_object* v_f_1216_, lean_object* v_m_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_apply_1(v_m_1217_, lean_box(0));
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_f_1216_);
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1236_; 
v_a_1228_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1230_ = v___x_1219_;
v_isShared_1231_ = v_isSharedCheck_1236_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1219_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1236_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = lean_apply_1(v_f_1216_, v_a_1228_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1232_);
v___x_1234_ = v___x_1230_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_adapt_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1216_ = stack[3].m_obj;
lean_object* v_m_1217_ = stack[4].m_obj;
lean_object* v_res_1237_;
v_res_1237_ = l_EIO_adapt(lean_box(0), lean_box(0), lean_box(0), v_f_1216_, v_m_1217_);
stack->m_obj
 = v_res_1237_;
}
LEAN_EXPORT lean_object* l_EIO_adapt___boxed(lean_object* v_00_u03b5_1238_, lean_object* v_00_u03b5_x27_1239_, lean_object* v_00_u03b1_1240_, lean_object* v_f_1241_, lean_object* v_m_1242_, lean_object* v_s_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_EIO_adapt(v_00_u03b5_1238_, v_00_u03b5_x27_1239_, v_00_u03b1_1240_, v_f_1241_, v_m_1242_);
return v_res_1244_;
}
}
lean_object* l_EIO_adaptExcept___redArg(lean_object* v_f_1245_, lean_object* v_m_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_apply_1(v_m_1246_, lean_box(0));
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_f_1245_);
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1265_; 
v_a_1257_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1259_ = v___x_1248_;
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1248_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_apply_1(v_f_1245_, v_a_1257_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1261_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_adaptExcept___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1245_ = stack[0].m_obj;
lean_object* v_m_1246_ = stack[1].m_obj;
lean_object* v_res_1266_;
v_res_1266_ = l_EIO_adaptExcept___redArg(v_f_1245_, v_m_1246_);
stack->m_obj
 = v_res_1266_;
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept___redArg___boxed(lean_object* v_f_1267_, lean_object* v_m_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_EIO_adaptExcept___redArg(v_f_1267_, v_m_1268_);
return v_res_1270_;
}
}
lean_object* l_EIO_adaptExcept(lean_object* v_00_u03b5_1271_, lean_object* v_00_u03b5_x27_1272_, lean_object* v_00_u03b1_1273_, lean_object* v_f_1274_, lean_object* v_m_1275_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_apply_1(v_m_1275_, lean_box(0));
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v_f_1274_);
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1294_; 
v_a_1286_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1288_ = v___x_1277_;
v_isShared_1289_ = v_isSharedCheck_1294_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1277_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1294_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1290_ = lean_apply_1(v_f_1274_, v_a_1286_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1290_);
v___x_1292_ = v___x_1288_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_adaptExcept_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1274_ = stack[3].m_obj;
lean_object* v_m_1275_ = stack[4].m_obj;
lean_object* v_res_1295_;
v_res_1295_ = l_EIO_adaptExcept(lean_box(0), lean_box(0), lean_box(0), v_f_1274_, v_m_1275_);
stack->m_obj
 = v_res_1295_;
}
LEAN_EXPORT lean_object* l_EIO_adaptExcept___boxed(lean_object* v_00_u03b5_1296_, lean_object* v_00_u03b5_x27_1297_, lean_object* v_00_u03b1_1298_, lean_object* v_f_1299_, lean_object* v_m_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_EIO_adaptExcept(v_00_u03b5_1296_, v_00_u03b5_x27_1297_, v_00_u03b1_1298_, v_f_1299_, v_m_1300_);
return v_res_1302_;
}
}
lean_object* l_BaseIO_toIO___redArg(lean_object* v_act_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_apply_1(v_act_1303_, lean_box(0));
v___x_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT void l_BaseIO_toIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_1303_ = stack[0].m_obj;
lean_object* v_res_1307_;
v_res_1307_ = l_BaseIO_toIO___redArg(v_act_1303_);
stack->m_obj
 = v_res_1307_;
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___redArg___boxed(lean_object* v_act_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_BaseIO_toIO___redArg(v_act_1308_);
return v_res_1310_;
}
}
lean_object* l_BaseIO_toIO(lean_object* v_00_u03b1_1311_, lean_object* v_act_1312_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_apply_1(v_act_1312_, lean_box(0));
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT void l_BaseIO_toIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_1312_ = stack[1].m_obj;
lean_object* v_res_1316_;
v_res_1316_ = l_BaseIO_toIO(lean_box(0), v_act_1312_);
stack->m_obj
 = v_res_1316_;
}
LEAN_EXPORT lean_object* l_BaseIO_toIO___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_act_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_BaseIO_toIO(v_00_u03b1_1317_, v_act_1318_);
return v_res_1320_;
}
}
lean_object* l_EIO_toIO___redArg(lean_object* v_f_1321_, lean_object* v_act_1322_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_apply_1(v_act_1322_, lean_box(0));
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v_f_1321_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1341_; 
v_a_1333_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1335_ = v___x_1324_;
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1324_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = lean_apply_1(v_f_1321_, v_a_1333_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1337_);
v___x_1339_ = v___x_1335_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT void l_EIO_toIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1321_ = stack[0].m_obj;
lean_object* v_act_1322_ = stack[1].m_obj;
lean_object* v_res_1342_;
v_res_1342_ = l_EIO_toIO___redArg(v_f_1321_, v_act_1322_);
stack->m_obj
 = v_res_1342_;
}
LEAN_EXPORT lean_object* l_EIO_toIO___redArg___boxed(lean_object* v_f_1343_, lean_object* v_act_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_EIO_toIO___redArg(v_f_1343_, v_act_1344_);
return v_res_1346_;
}
}
lean_object* l_EIO_toIO(lean_object* v_00_u03b5_1347_, lean_object* v_00_u03b1_1348_, lean_object* v_f_1349_, lean_object* v_act_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_apply_1(v_act_1350_, lean_box(0));
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v_f_1349_);
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1369_; 
v_a_1361_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1363_ = v___x_1352_;
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1352_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = lean_apply_1(v_f_1349_, v_a_1361_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_toIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1349_ = stack[2].m_obj;
lean_object* v_act_1350_ = stack[3].m_obj;
lean_object* v_res_1370_;
v_res_1370_ = l_EIO_toIO(lean_box(0), lean_box(0), v_f_1349_, v_act_1350_);
stack->m_obj
 = v_res_1370_;
}
LEAN_EXPORT lean_object* l_EIO_toIO___boxed(lean_object* v_00_u03b5_1371_, lean_object* v_00_u03b1_1372_, lean_object* v_f_1373_, lean_object* v_act_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_EIO_toIO(v_00_u03b5_1371_, v_00_u03b1_1372_, v_f_1373_, v_act_1374_);
return v_res_1376_;
}
}
lean_object* l_EIO_toIO_x27___redArg(lean_object* v_act_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_apply_1(v_act_1377_, lean_box(0));
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1388_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_a_1380_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1384_);
v___x_1386_ = v___x_1382_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1397_; 
v_a_1389_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1391_ = v___x_1379_;
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1379_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_a_1389_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1393_);
v___x_1395_ = v___x_1391_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_toIO_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_1377_ = stack[0].m_obj;
lean_object* v_res_1398_;
v_res_1398_ = l_EIO_toIO_x27___redArg(v_act_1377_);
stack->m_obj
 = v_res_1398_;
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___redArg___boxed(lean_object* v_act_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_EIO_toIO_x27___redArg(v_act_1399_);
return v_res_1401_;
}
}
lean_object* l_EIO_toIO_x27(lean_object* v_00_u03b5_1402_, lean_object* v_00_u03b1_1403_, lean_object* v_act_1404_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_apply_1(v_act_1404_, lean_box(0));
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1415_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_a_1407_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
v_a_1416_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v___x_1406_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1406_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_a_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set_tag(v___x_1418_, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_toIO_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_1404_ = stack[2].m_obj;
lean_object* v_res_1425_;
v_res_1425_ = l_EIO_toIO_x27(lean_box(0), lean_box(0), v_act_1404_);
stack->m_obj
 = v_res_1425_;
}
LEAN_EXPORT lean_object* l_EIO_toIO_x27___boxed(lean_object* v_00_u03b5_1426_, lean_object* v_00_u03b1_1427_, lean_object* v_act_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_EIO_toIO_x27(v_00_u03b5_1426_, v_00_u03b1_1427_, v_act_1428_);
return v_res_1430_;
}
}
lean_object* l_IO_toEIO___redArg(lean_object* v_f_1431_, lean_object* v_act_1432_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_apply_1(v_act_1432_, lean_box(0));
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_f_1431_);
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1451_; 
v_a_1443_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1445_ = v___x_1434_;
v_isShared_1446_ = v_isSharedCheck_1451_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1434_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1451_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1447_ = lean_apply_1(v_f_1431_, v_a_1443_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1447_);
v___x_1449_ = v___x_1445_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
LEAN_EXPORT void l_IO_toEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1431_ = stack[0].m_obj;
lean_object* v_act_1432_ = stack[1].m_obj;
lean_object* v_res_1452_;
v_res_1452_ = l_IO_toEIO___redArg(v_f_1431_, v_act_1432_);
stack->m_obj
 = v_res_1452_;
}
LEAN_EXPORT lean_object* l_IO_toEIO___redArg___boxed(lean_object* v_f_1453_, lean_object* v_act_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_IO_toEIO___redArg(v_f_1453_, v_act_1454_);
return v_res_1456_;
}
}
lean_object* l_IO_toEIO(lean_object* v_00_u03b5_1457_, lean_object* v_00_u03b1_1458_, lean_object* v_f_1459_, lean_object* v_act_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_apply_1(v_act_1460_, lean_box(0));
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_f_1459_);
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1479_; 
v_a_1471_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1473_ = v___x_1462_;
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1462_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1475_ = lean_apply_1(v_f_1459_, v_a_1471_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1475_);
v___x_1477_ = v___x_1473_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
LEAN_EXPORT void l_IO_toEIO_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1459_ = stack[2].m_obj;
lean_object* v_act_1460_ = stack[3].m_obj;
lean_object* v_res_1480_;
v_res_1480_ = l_IO_toEIO(lean_box(0), lean_box(0), v_f_1459_, v_act_1460_);
stack->m_obj
 = v_res_1480_;
}
LEAN_EXPORT lean_object* l_IO_toEIO___boxed(lean_object* v_00_u03b5_1481_, lean_object* v_00_u03b1_1482_, lean_object* v_f_1483_, lean_object* v_act_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_IO_toEIO(v_00_u03b5_1481_, v_00_u03b1_1482_, v_f_1483_, v_act_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO___redArg(lean_object* v_fn_1487_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_apply_1(v_fn_1487_, v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_unsafeBaseIO(lean_object* v_00_u03b1_1490_, lean_object* v_fn_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_unsafeBaseIO___redArg(v_fn_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_unsafeEIO___redArg(lean_object* v_fn_1493_){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1494_, 0, lean_box(0));
lean_closure_set(v___x_1494_, 1, lean_box(0));
lean_closure_set(v___x_1494_, 2, v_fn_1493_);
v___x_1495_ = l_unsafeBaseIO___redArg(v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_unsafeEIO(lean_object* v_00_u03b5_1496_, lean_object* v_00_u03b1_1497_, lean_object* v_fn_1498_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1499_, 0, lean_box(0));
lean_closure_set(v___x_1499_, 1, lean_box(0));
lean_closure_set(v___x_1499_, 2, v_fn_1498_);
v___x_1500_ = l_unsafeBaseIO___redArg(v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_unsafeIO___redArg(lean_object* v_fn_1501_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1502_, 0, lean_box(0));
lean_closure_set(v___x_1502_, 1, lean_box(0));
lean_closure_set(v___x_1502_, 2, v_fn_1501_);
v___x_1503_ = l_unsafeBaseIO___redArg(v___x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_unsafeIO(lean_object* v_00_u03b1_1504_, lean_object* v_fn_1505_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1506_, 0, lean_box(0));
lean_closure_set(v___x_1506_, 1, lean_box(0));
lean_closure_set(v___x_1506_, 2, v_fn_1505_);
v___x_1507_ = l_unsafeBaseIO___redArg(v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT void l_timeit_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1509_ = stack[1].m_obj;
lean_object* v_fn_1510_ = stack[2].m_obj;
lean_object* v_res_1512_;
v_res_1512_ = lean_io_timeit(v_msg_1509_, v_fn_1510_);
stack->m_obj
 = v_res_1512_;
}
LEAN_EXPORT lean_object* l_timeit___boxed(lean_object* v_00_u03b1_1513_, lean_object* v_msg_1514_, lean_object* v_fn_1515_, lean_object* v_a_00___x40___internal___hyg_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = lean_io_timeit(v_msg_1514_, v_fn_1515_);
lean_dec_ref(v_msg_1514_);
return v_res_1517_;
}
}
LEAN_EXPORT void l_allocprof_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1519_ = stack[1].m_obj;
lean_object* v_fn_1520_ = stack[2].m_obj;
lean_object* v_res_1522_;
v_res_1522_ = lean_io_allocprof(v_msg_1519_, v_fn_1520_);
stack->m_obj
 = v_res_1522_;
}
LEAN_EXPORT lean_object* l_allocprof___boxed(lean_object* v_00_u03b1_1523_, lean_object* v_msg_1524_, lean_object* v_fn_1525_, lean_object* v_a_00___x40___internal___hyg_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = lean_io_allocprof(v_msg_1524_, v_fn_1525_);
lean_dec_ref(v_msg_1524_);
return v_res_1527_;
}
}
LEAN_EXPORT void l_IO_initializing_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_1529_;
v_res_1529_ = lean_io_initializing();
stack->m_num = v_res_1529_;
}
LEAN_EXPORT lean_object* l_IO_initializing___boxed(lean_object* v_a_00___x40___internal___hyg_1530_){
_start:
{
uint8_t v_res_1531_; lean_object* v_r_1532_; 
v_res_1531_ = lean_io_initializing();
v_r_1532_ = lean_box(v_res_1531_);
return v_r_1532_;
}
}
LEAN_EXPORT void l_BaseIO_asTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_1534_ = stack[1].m_obj;
lean_object* v_prio_1535_ = stack[2].m_obj;
lean_object* v_res_1537_;
v_res_1537_ = lean_io_as_task(v_act_1534_, v_prio_1535_);
stack->m_obj
 = v_res_1537_;
}
LEAN_EXPORT lean_object* l_BaseIO_asTask___boxed(lean_object* v_00_u03b1_1538_, lean_object* v_act_1539_, lean_object* v_prio_1540_, lean_object* v_a_00___x40___internal___hyg_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = lean_io_as_task(v_act_1539_, v_prio_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT void l_BaseIO_mapTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1545_ = stack[2].m_obj;
lean_object* v_t_1546_ = stack[3].m_obj;
lean_object* v_prio_1547_ = stack[4].m_obj;
uint8_t v_sync_1548_ = stack[5].m_num;
lean_object* v_res_1550_;
v_res_1550_ = lean_io_map_task(v_f_1545_, v_t_1546_, v_prio_1547_, v_sync_1548_);
stack->m_obj
 = v_res_1550_;
}
LEAN_EXPORT lean_object* l_BaseIO_mapTask___boxed(lean_object* v_00_u03b1_1551_, lean_object* v_00_u03b2_1552_, lean_object* v_f_1553_, lean_object* v_t_1554_, lean_object* v_prio_1555_, lean_object* v_sync_1556_, lean_object* v_a_00___x40___internal___hyg_1557_){
_start:
{
uint8_t v_sync_boxed_1558_; lean_object* v_res_1559_; 
v_sync_boxed_1558_ = lean_unbox(v_sync_1556_);
v_res_1559_ = lean_io_map_task(v_f_1553_, v_t_1554_, v_prio_1555_, v_sync_boxed_1558_);
return v_res_1559_;
}
}
LEAN_EXPORT void l_BaseIO_bindTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1562_ = stack[2].m_obj;
lean_object* v_f_1563_ = stack[3].m_obj;
lean_object* v_prio_1564_ = stack[4].m_obj;
uint8_t v_sync_1565_ = stack[5].m_num;
lean_object* v_res_1567_;
v_res_1567_ = lean_io_bind_task(v_t_1562_, v_f_1563_, v_prio_1564_, v_sync_1565_);
stack->m_obj
 = v_res_1567_;
}
LEAN_EXPORT lean_object* l_BaseIO_bindTask___boxed(lean_object* v_00_u03b1_1568_, lean_object* v_00_u03b2_1569_, lean_object* v_t_1570_, lean_object* v_f_1571_, lean_object* v_prio_1572_, lean_object* v_sync_1573_, lean_object* v_a_00___x40___internal___hyg_1574_){
_start:
{
uint8_t v_sync_boxed_1575_; lean_object* v_res_1576_; 
v_sync_boxed_1575_ = lean_unbox(v_sync_1573_);
v_res_1576_ = lean_io_bind_task(v_t_1570_, v_f_1571_, v_prio_1572_, v_sync_boxed_1575_);
return v_res_1576_;
}
}
lean_object* l_BaseIO_chainTask___redArg(lean_object* v_t_1577_, lean_object* v_f_1578_, lean_object* v_prio_1579_, uint8_t v_sync_1580_){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_box(0);
v___x_1583_ = lean_io_map_task(v_f_1578_, v_t_1577_, v_prio_1579_, v_sync_1580_);
lean_dec_ref(v___x_1583_);
return v___x_1582_;
}
}
LEAN_EXPORT void l_BaseIO_chainTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1577_ = stack[0].m_obj;
lean_object* v_f_1578_ = stack[1].m_obj;
lean_object* v_prio_1579_ = stack[2].m_obj;
uint8_t v_sync_1580_ = stack[3].m_num;
lean_object* v_res_1584_;
v_res_1584_ = l_BaseIO_chainTask___redArg(v_t_1577_, v_f_1578_, v_prio_1579_, v_sync_1580_);
stack->m_obj
 = v_res_1584_;
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___redArg___boxed(lean_object* v_t_1585_, lean_object* v_f_1586_, lean_object* v_prio_1587_, lean_object* v_sync_1588_, lean_object* v_a_1589_){
_start:
{
uint8_t v_sync_boxed_1590_; lean_object* v_res_1591_; 
v_sync_boxed_1590_ = lean_unbox(v_sync_1588_);
v_res_1591_ = l_BaseIO_chainTask___redArg(v_t_1585_, v_f_1586_, v_prio_1587_, v_sync_boxed_1590_);
return v_res_1591_;
}
}
lean_object* l_BaseIO_chainTask(lean_object* v_00_u03b1_1592_, lean_object* v_t_1593_, lean_object* v_f_1594_, lean_object* v_prio_1595_, uint8_t v_sync_1596_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_BaseIO_chainTask___redArg(v_t_1593_, v_f_1594_, v_prio_1595_, v_sync_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT void l_BaseIO_chainTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1593_ = stack[1].m_obj;
lean_object* v_f_1594_ = stack[2].m_obj;
lean_object* v_prio_1595_ = stack[3].m_obj;
uint8_t v_sync_1596_ = stack[4].m_num;
lean_object* v_res_1599_;
v_res_1599_ = l_BaseIO_chainTask(lean_box(0), v_t_1593_, v_f_1594_, v_prio_1595_, v_sync_1596_);
stack->m_obj
 = v_res_1599_;
}
LEAN_EXPORT lean_object* l_BaseIO_chainTask___boxed(lean_object* v_00_u03b1_1600_, lean_object* v_t_1601_, lean_object* v_f_1602_, lean_object* v_prio_1603_, lean_object* v_sync_1604_, lean_object* v_a_1605_){
_start:
{
uint8_t v_sync_boxed_1606_; lean_object* v_res_1607_; 
v_sync_boxed_1606_ = lean_unbox(v_sync_1604_);
v_res_1607_ = l_BaseIO_chainTask(v_00_u03b1_1600_, v_t_1601_, v_f_1602_, v_prio_1603_, v_sync_boxed_1606_);
return v_res_1607_;
}
}
lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(lean_object* v_x_1608_, lean_object* v_f_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1612_, 0, v_a_1610_);
lean_ctor_set(v___x_1612_, 1, v_x_1608_);
v___x_1613_ = l_List_reverse___redArg(v___x_1612_);
v___x_1614_ = lean_apply_2(v_f_1609_, v___x_1613_, lean_box(0));
return v___x_1614_;
}
}
LEAN_EXPORT void l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1608_ = stack[0].m_obj;
lean_object* v_f_1609_ = stack[1].m_obj;
lean_object* v_a_1610_ = stack[2].m_obj;
lean_object* v_res_1615_;
v_res_1615_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(v_x_1608_, v_f_1609_, v_a_1610_);
stack->m_obj
 = v_res_1615_;
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed(lean_object* v_x_1616_, lean_object* v_f_1617_, lean_object* v_a_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0(v_x_1616_, v_f_1617_, v_a_1618_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed(lean_object* v_x_1621_, lean_object* v_f_1622_, lean_object* v_prio_1623_, lean_object* v_sync_1624_, lean_object* v_tail_1625_, lean_object* v_a_1626_, lean_object* v___y_1627_){
_start:
{
uint8_t v_sync_boxed_1628_; lean_object* v_res_1629_; 
v_sync_boxed_1628_ = lean_unbox(v_sync_1624_);
v_res_1629_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(v_x_1621_, v_f_1622_, v_prio_1623_, v_sync_boxed_1628_, v_tail_1625_, v_a_1626_);
return v_res_1629_;
}
}
lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(lean_object* v_f_1630_, lean_object* v_prio_1631_, uint8_t v_sync_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_){
_start:
{
if (lean_obj_tag(v_x_1633_) == 0)
{
if (v_sync_1632_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = l_List_reverse___redArg(v_x_1634_);
v___x_1637_ = lean_apply_1(v_f_1630_, v___x_1636_);
v___x_1638_ = lean_io_as_task(v___x_1637_, v_prio_1631_);
return v___x_1638_;
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec(v_prio_1631_);
v___x_1639_ = l_List_reverse___redArg(v_x_1634_);
v___x_1640_ = lean_apply_2(v_f_1630_, v___x_1639_, lean_box(0));
v___x_1641_ = lean_task_pure(v___x_1640_);
return v___x_1641_;
}
}
else
{
lean_object* v_tail_1642_; 
v_tail_1642_ = lean_ctor_get(v_x_1633_, 1);
if (lean_obj_tag(v_tail_1642_) == 0)
{
lean_object* v_head_1643_; lean_object* v___f_1644_; lean_object* v___x_1645_; 
v_head_1643_ = lean_ctor_get(v_x_1633_, 0);
lean_inc(v_head_1643_);
lean_dec_ref_known(v_x_1633_, 2);
v___f_1644_ = lean_alloc_closure((void*)(l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1644_, 0, v_x_1634_);
lean_closure_set(v___f_1644_, 1, v_f_1630_);
v___x_1645_ = lean_io_map_task(v___f_1644_, v_head_1643_, v_prio_1631_, v_sync_1632_);
return v___x_1645_;
}
else
{
lean_object* v_head_1646_; lean_object* v___x_1647_; lean_object* v___f_1648_; lean_object* v___x_1649_; 
lean_inc(v_tail_1642_);
v_head_1646_ = lean_ctor_get(v_x_1633_, 0);
lean_inc(v_head_1646_);
lean_dec_ref_known(v_x_1633_, 2);
v___x_1647_ = lean_box(v_sync_1632_);
lean_inc(v_prio_1631_);
v___f_1648_ = lean_alloc_closure((void*)(l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_1648_, 0, v_x_1634_);
lean_closure_set(v___f_1648_, 1, v_f_1630_);
lean_closure_set(v___f_1648_, 2, v_prio_1631_);
lean_closure_set(v___f_1648_, 3, v___x_1647_);
lean_closure_set(v___f_1648_, 4, v_tail_1642_);
v___x_1649_ = lean_io_bind_task(v_head_1646_, v___f_1648_, v_prio_1631_, v_sync_1632_);
return v___x_1649_;
}
}
}
}
LEAN_EXPORT void l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1630_ = stack[0].m_obj;
lean_object* v_prio_1631_ = stack[1].m_obj;
uint8_t v_sync_1632_ = stack[2].m_num;
lean_object* v_x_1633_ = stack[3].m_obj;
lean_object* v_x_1634_ = stack[4].m_obj;
lean_object* v_res_1650_;
v_res_1650_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_1630_, v_prio_1631_, v_sync_1632_, v_x_1633_, v_x_1634_);
stack->m_obj
 = v_res_1650_;
}
lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(lean_object* v_x_1651_, lean_object* v_f_1652_, lean_object* v_prio_1653_, uint8_t v_sync_1654_, lean_object* v_tail_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1658_, 0, v_a_1656_);
lean_ctor_set(v___x_1658_, 1, v_x_1651_);
v___x_1659_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_1652_, v_prio_1653_, v_sync_1654_, v_tail_1655_, v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT void l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1651_ = stack[0].m_obj;
lean_object* v_f_1652_ = stack[1].m_obj;
lean_object* v_prio_1653_ = stack[2].m_obj;
uint8_t v_sync_1654_ = stack[3].m_num;
lean_object* v_tail_1655_ = stack[4].m_obj;
lean_object* v_a_1656_ = stack[5].m_obj;
lean_object* v_res_1660_;
v_res_1660_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___lam__1(v_x_1651_, v_f_1652_, v_prio_1653_, v_sync_1654_, v_tail_1655_, v_a_1656_);
stack->m_obj
 = v_res_1660_;
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg___boxed(lean_object* v_f_1661_, lean_object* v_prio_1662_, lean_object* v_sync_1663_, lean_object* v_x_1664_, lean_object* v_x_1665_, lean_object* v_a_1666_){
_start:
{
uint8_t v_sync_boxed_1667_; lean_object* v_res_1668_; 
v_sync_boxed_1667_ = lean_unbox(v_sync_1663_);
v_res_1668_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_1661_, v_prio_1662_, v_sync_boxed_1667_, v_x_1664_, v_x_1665_);
return v_res_1668_;
}
}
lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go(lean_object* v_00_u03b1_1669_, lean_object* v_00_u03b2_1670_, lean_object* v_f_1671_, lean_object* v_prio_1672_, uint8_t v_sync_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_1671_, v_prio_1672_, v_sync_1673_, v_x_1674_, v_x_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT void l___private_Init_System_IO_0__BaseIO_mapTasks_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1671_ = stack[2].m_obj;
lean_object* v_prio_1672_ = stack[3].m_obj;
uint8_t v_sync_1673_ = stack[4].m_num;
lean_object* v_x_1674_ = stack[5].m_obj;
lean_object* v_x_1675_ = stack[6].m_obj;
lean_object* v_res_1678_;
v_res_1678_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go(lean_box(0), lean_box(0), v_f_1671_, v_prio_1672_, v_sync_1673_, v_x_1674_, v_x_1675_);
stack->m_obj
 = v_res_1678_;
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__BaseIO_mapTasks_go___boxed(lean_object* v_00_u03b1_1679_, lean_object* v_00_u03b2_1680_, lean_object* v_f_1681_, lean_object* v_prio_1682_, lean_object* v_sync_1683_, lean_object* v_x_1684_, lean_object* v_x_1685_, lean_object* v_a_1686_){
_start:
{
uint8_t v_sync_boxed_1687_; lean_object* v_res_1688_; 
v_sync_boxed_1687_ = lean_unbox(v_sync_1683_);
v_res_1688_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go(v_00_u03b1_1679_, v_00_u03b2_1680_, v_f_1681_, v_prio_1682_, v_sync_boxed_1687_, v_x_1684_, v_x_1685_);
return v_res_1688_;
}
}
lean_object* l_BaseIO_mapTasks___redArg(lean_object* v_f_1689_, lean_object* v_tasks_1690_, lean_object* v_prio_1691_, uint8_t v_sync_1692_){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_box(0);
v___x_1695_ = l___private_Init_System_IO_0__BaseIO_mapTasks_go___redArg(v_f_1689_, v_prio_1691_, v_sync_1692_, v_tasks_1690_, v___x_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT void l_BaseIO_mapTasks___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1689_ = stack[0].m_obj;
lean_object* v_tasks_1690_ = stack[1].m_obj;
lean_object* v_prio_1691_ = stack[2].m_obj;
uint8_t v_sync_1692_ = stack[3].m_num;
lean_object* v_res_1696_;
v_res_1696_ = l_BaseIO_mapTasks___redArg(v_f_1689_, v_tasks_1690_, v_prio_1691_, v_sync_1692_);
stack->m_obj
 = v_res_1696_;
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___redArg___boxed(lean_object* v_f_1697_, lean_object* v_tasks_1698_, lean_object* v_prio_1699_, lean_object* v_sync_1700_, lean_object* v_a_1701_){
_start:
{
uint8_t v_sync_boxed_1702_; lean_object* v_res_1703_; 
v_sync_boxed_1702_ = lean_unbox(v_sync_1700_);
v_res_1703_ = l_BaseIO_mapTasks___redArg(v_f_1697_, v_tasks_1698_, v_prio_1699_, v_sync_boxed_1702_);
return v_res_1703_;
}
}
lean_object* l_BaseIO_mapTasks(lean_object* v_00_u03b1_1704_, lean_object* v_00_u03b2_1705_, lean_object* v_f_1706_, lean_object* v_tasks_1707_, lean_object* v_prio_1708_, uint8_t v_sync_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_BaseIO_mapTasks___redArg(v_f_1706_, v_tasks_1707_, v_prio_1708_, v_sync_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT void l_BaseIO_mapTasks_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1706_ = stack[2].m_obj;
lean_object* v_tasks_1707_ = stack[3].m_obj;
lean_object* v_prio_1708_ = stack[4].m_obj;
uint8_t v_sync_1709_ = stack[5].m_num;
lean_object* v_res_1712_;
v_res_1712_ = l_BaseIO_mapTasks(lean_box(0), lean_box(0), v_f_1706_, v_tasks_1707_, v_prio_1708_, v_sync_1709_);
stack->m_obj
 = v_res_1712_;
}
LEAN_EXPORT lean_object* l_BaseIO_mapTasks___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_f_1715_, lean_object* v_tasks_1716_, lean_object* v_prio_1717_, lean_object* v_sync_1718_, lean_object* v_a_1719_){
_start:
{
uint8_t v_sync_boxed_1720_; lean_object* v_res_1721_; 
v_sync_boxed_1720_ = lean_unbox(v_sync_1718_);
v_res_1721_ = l_BaseIO_mapTasks(v_00_u03b1_1713_, v_00_u03b2_1714_, v_f_1715_, v_tasks_1716_, v_prio_1717_, v_sync_boxed_1720_);
return v_res_1721_;
}
}
lean_object* l_EIO_asTask___redArg(lean_object* v_act_1722_, lean_object* v_prio_1723_){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1725_, 0, lean_box(0));
lean_closure_set(v___x_1725_, 1, lean_box(0));
lean_closure_set(v___x_1725_, 2, v_act_1722_);
v___x_1726_ = lean_io_as_task(v___x_1725_, v_prio_1723_);
return v___x_1726_;
}
}
LEAN_EXPORT void l_EIO_asTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_1722_ = stack[0].m_obj;
lean_object* v_prio_1723_ = stack[1].m_obj;
lean_object* v_res_1727_;
v_res_1727_ = l_EIO_asTask___redArg(v_act_1722_, v_prio_1723_);
stack->m_obj
 = v_res_1727_;
}
LEAN_EXPORT lean_object* l_EIO_asTask___redArg___boxed(lean_object* v_act_1728_, lean_object* v_prio_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_EIO_asTask___redArg(v_act_1728_, v_prio_1729_);
return v_res_1731_;
}
}
lean_object* l_EIO_asTask(lean_object* v_00_u03b5_1732_, lean_object* v_00_u03b1_1733_, lean_object* v_act_1734_, lean_object* v_prio_1735_){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_1737_, 0, lean_box(0));
lean_closure_set(v___x_1737_, 1, lean_box(0));
lean_closure_set(v___x_1737_, 2, v_act_1734_);
v___x_1738_ = lean_io_as_task(v___x_1737_, v_prio_1735_);
return v___x_1738_;
}
}
LEAN_EXPORT void l_EIO_asTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_1734_ = stack[2].m_obj;
lean_object* v_prio_1735_ = stack[3].m_obj;
lean_object* v_res_1739_;
v_res_1739_ = l_EIO_asTask(lean_box(0), lean_box(0), v_act_1734_, v_prio_1735_);
stack->m_obj
 = v_res_1739_;
}
LEAN_EXPORT lean_object* l_EIO_asTask___boxed(lean_object* v_00_u03b5_1740_, lean_object* v_00_u03b1_1741_, lean_object* v_act_1742_, lean_object* v_prio_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_EIO_asTask(v_00_u03b5_1740_, v_00_u03b1_1741_, v_act_1742_, v_prio_1743_);
return v_res_1745_;
}
}
lean_object* l_EIO_mapTask___redArg___lam__0(lean_object* v_f_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_apply_2(v_f_1746_, v_a_1747_, lean_box(0));
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set_tag(v___x_1752_, 1);
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
v_a_1758_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1749_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1749_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 0);
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_mapTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1746_ = stack[0].m_obj;
lean_object* v_a_1747_ = stack[1].m_obj;
lean_object* v_res_1766_;
v_res_1766_ = l_EIO_mapTask___redArg___lam__0(v_f_1746_, v_a_1747_);
stack->m_obj
 = v_res_1766_;
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___lam__0___boxed(lean_object* v_f_1767_, lean_object* v_a_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_EIO_mapTask___redArg___lam__0(v_f_1767_, v_a_1768_);
return v_res_1770_;
}
}
lean_object* l_EIO_mapTask___redArg(lean_object* v_f_1771_, lean_object* v_t_1772_, lean_object* v_prio_1773_, uint8_t v_sync_1774_){
_start:
{
lean_object* v___f_1776_; lean_object* v___x_1777_; 
v___f_1776_ = lean_alloc_closure((void*)(l_EIO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1776_, 0, v_f_1771_);
v___x_1777_ = lean_io_map_task(v___f_1776_, v_t_1772_, v_prio_1773_, v_sync_1774_);
return v___x_1777_;
}
}
LEAN_EXPORT void l_EIO_mapTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1771_ = stack[0].m_obj;
lean_object* v_t_1772_ = stack[1].m_obj;
lean_object* v_prio_1773_ = stack[2].m_obj;
uint8_t v_sync_1774_ = stack[3].m_num;
lean_object* v_res_1778_;
v_res_1778_ = l_EIO_mapTask___redArg(v_f_1771_, v_t_1772_, v_prio_1773_, v_sync_1774_);
stack->m_obj
 = v_res_1778_;
}
LEAN_EXPORT lean_object* l_EIO_mapTask___redArg___boxed(lean_object* v_f_1779_, lean_object* v_t_1780_, lean_object* v_prio_1781_, lean_object* v_sync_1782_, lean_object* v_a_1783_){
_start:
{
uint8_t v_sync_boxed_1784_; lean_object* v_res_1785_; 
v_sync_boxed_1784_ = lean_unbox(v_sync_1782_);
v_res_1785_ = l_EIO_mapTask___redArg(v_f_1779_, v_t_1780_, v_prio_1781_, v_sync_boxed_1784_);
return v_res_1785_;
}
}
lean_object* l_EIO_mapTask(lean_object* v_00_u03b1_1786_, lean_object* v_00_u03b5_1787_, lean_object* v_00_u03b2_1788_, lean_object* v_f_1789_, lean_object* v_t_1790_, lean_object* v_prio_1791_, uint8_t v_sync_1792_){
_start:
{
lean_object* v___f_1794_; lean_object* v___x_1795_; 
v___f_1794_ = lean_alloc_closure((void*)(l_EIO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1794_, 0, v_f_1789_);
v___x_1795_ = lean_io_map_task(v___f_1794_, v_t_1790_, v_prio_1791_, v_sync_1792_);
return v___x_1795_;
}
}
LEAN_EXPORT void l_EIO_mapTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1789_ = stack[3].m_obj;
lean_object* v_t_1790_ = stack[4].m_obj;
lean_object* v_prio_1791_ = stack[5].m_obj;
uint8_t v_sync_1792_ = stack[6].m_num;
lean_object* v_res_1796_;
v_res_1796_ = l_EIO_mapTask(lean_box(0), lean_box(0), lean_box(0), v_f_1789_, v_t_1790_, v_prio_1791_, v_sync_1792_);
stack->m_obj
 = v_res_1796_;
}
LEAN_EXPORT lean_object* l_EIO_mapTask___boxed(lean_object* v_00_u03b1_1797_, lean_object* v_00_u03b5_1798_, lean_object* v_00_u03b2_1799_, lean_object* v_f_1800_, lean_object* v_t_1801_, lean_object* v_prio_1802_, lean_object* v_sync_1803_, lean_object* v_a_1804_){
_start:
{
uint8_t v_sync_boxed_1805_; lean_object* v_res_1806_; 
v_sync_boxed_1805_ = lean_unbox(v_sync_1803_);
v_res_1806_ = l_EIO_mapTask(v_00_u03b1_1797_, v_00_u03b5_1798_, v_00_u03b2_1799_, v_f_1800_, v_t_1801_, v_prio_1802_, v_sync_boxed_1805_);
return v_res_1806_;
}
}
lean_object* l_EIO_bindTask___redArg___lam__0(lean_object* v_f_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_apply_2(v_f_1807_, v_a_1808_, lean_box(0));
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
return v_a_1811_;
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1820_; 
v_a_1812_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1814_ = v___x_1810_;
v_isShared_1815_ = v_isSharedCheck_1820_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1810_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1820_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 0);
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_task_pure(v___x_1817_);
return v___x_1818_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_bindTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1807_ = stack[0].m_obj;
lean_object* v_a_1808_ = stack[1].m_obj;
lean_object* v_res_1821_;
v_res_1821_ = l_EIO_bindTask___redArg___lam__0(v_f_1807_, v_a_1808_);
stack->m_obj
 = v_res_1821_;
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___lam__0___boxed(lean_object* v_f_1822_, lean_object* v_a_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_EIO_bindTask___redArg___lam__0(v_f_1822_, v_a_1823_);
return v_res_1825_;
}
}
lean_object* l_EIO_bindTask___redArg(lean_object* v_t_1826_, lean_object* v_f_1827_, lean_object* v_prio_1828_, uint8_t v_sync_1829_){
_start:
{
lean_object* v___f_1831_; lean_object* v___x_1832_; 
v___f_1831_ = lean_alloc_closure((void*)(l_EIO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1831_, 0, v_f_1827_);
v___x_1832_ = lean_io_bind_task(v_t_1826_, v___f_1831_, v_prio_1828_, v_sync_1829_);
return v___x_1832_;
}
}
LEAN_EXPORT void l_EIO_bindTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1826_ = stack[0].m_obj;
lean_object* v_f_1827_ = stack[1].m_obj;
lean_object* v_prio_1828_ = stack[2].m_obj;
uint8_t v_sync_1829_ = stack[3].m_num;
lean_object* v_res_1833_;
v_res_1833_ = l_EIO_bindTask___redArg(v_t_1826_, v_f_1827_, v_prio_1828_, v_sync_1829_);
stack->m_obj
 = v_res_1833_;
}
LEAN_EXPORT lean_object* l_EIO_bindTask___redArg___boxed(lean_object* v_t_1834_, lean_object* v_f_1835_, lean_object* v_prio_1836_, lean_object* v_sync_1837_, lean_object* v_a_1838_){
_start:
{
uint8_t v_sync_boxed_1839_; lean_object* v_res_1840_; 
v_sync_boxed_1839_ = lean_unbox(v_sync_1837_);
v_res_1840_ = l_EIO_bindTask___redArg(v_t_1834_, v_f_1835_, v_prio_1836_, v_sync_boxed_1839_);
return v_res_1840_;
}
}
lean_object* l_EIO_bindTask(lean_object* v_00_u03b1_1841_, lean_object* v_00_u03b5_1842_, lean_object* v_00_u03b2_1843_, lean_object* v_t_1844_, lean_object* v_f_1845_, lean_object* v_prio_1846_, uint8_t v_sync_1847_){
_start:
{
lean_object* v___f_1849_; lean_object* v___x_1850_; 
v___f_1849_ = lean_alloc_closure((void*)(l_EIO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1849_, 0, v_f_1845_);
v___x_1850_ = lean_io_bind_task(v_t_1844_, v___f_1849_, v_prio_1846_, v_sync_1847_);
return v___x_1850_;
}
}
LEAN_EXPORT void l_EIO_bindTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1844_ = stack[3].m_obj;
lean_object* v_f_1845_ = stack[4].m_obj;
lean_object* v_prio_1846_ = stack[5].m_obj;
uint8_t v_sync_1847_ = stack[6].m_num;
lean_object* v_res_1851_;
v_res_1851_ = l_EIO_bindTask(lean_box(0), lean_box(0), lean_box(0), v_t_1844_, v_f_1845_, v_prio_1846_, v_sync_1847_);
stack->m_obj
 = v_res_1851_;
}
LEAN_EXPORT lean_object* l_EIO_bindTask___boxed(lean_object* v_00_u03b1_1852_, lean_object* v_00_u03b5_1853_, lean_object* v_00_u03b2_1854_, lean_object* v_t_1855_, lean_object* v_f_1856_, lean_object* v_prio_1857_, lean_object* v_sync_1858_, lean_object* v_a_1859_){
_start:
{
uint8_t v_sync_boxed_1860_; lean_object* v_res_1861_; 
v_sync_boxed_1860_ = lean_unbox(v_sync_1858_);
v_res_1861_ = l_EIO_bindTask(v_00_u03b1_1852_, v_00_u03b5_1853_, v_00_u03b2_1854_, v_t_1855_, v_f_1856_, v_prio_1857_, v_sync_boxed_1860_);
return v_res_1861_;
}
}
lean_object* l_EIO_chainTask___redArg___lam__0(lean_object* v_f_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_apply_2(v_f_1862_, v_a_1863_, lean_box(0));
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set_tag(v___x_1868_, 1);
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_a_1874_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1865_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1865_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set_tag(v___x_1876_, 0);
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_chainTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1862_ = stack[0].m_obj;
lean_object* v_a_1863_ = stack[1].m_obj;
lean_object* v_res_1882_;
v_res_1882_ = l_EIO_chainTask___redArg___lam__0(v_f_1862_, v_a_1863_);
stack->m_obj
 = v_res_1882_;
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___lam__0___boxed(lean_object* v_f_1883_, lean_object* v_a_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_EIO_chainTask___redArg___lam__0(v_f_1883_, v_a_1884_);
return v_res_1886_;
}
}
lean_object* l_EIO_chainTask___redArg(lean_object* v_t_1887_, lean_object* v_f_1888_, lean_object* v_prio_1889_, uint8_t v_sync_1890_){
_start:
{
lean_object* v___f_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___f_1892_ = lean_alloc_closure((void*)(l_EIO_chainTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1892_, 0, v_f_1888_);
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_io_map_task(v___f_1892_, v_t_1887_, v_prio_1889_, v_sync_1890_);
lean_dec_ref(v___x_1894_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
return v___x_1895_;
}
}
LEAN_EXPORT void l_EIO_chainTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1887_ = stack[0].m_obj;
lean_object* v_f_1888_ = stack[1].m_obj;
lean_object* v_prio_1889_ = stack[2].m_obj;
uint8_t v_sync_1890_ = stack[3].m_num;
lean_object* v_res_1896_;
v_res_1896_ = l_EIO_chainTask___redArg(v_t_1887_, v_f_1888_, v_prio_1889_, v_sync_1890_);
stack->m_obj
 = v_res_1896_;
}
LEAN_EXPORT lean_object* l_EIO_chainTask___redArg___boxed(lean_object* v_t_1897_, lean_object* v_f_1898_, lean_object* v_prio_1899_, lean_object* v_sync_1900_, lean_object* v_a_1901_){
_start:
{
uint8_t v_sync_boxed_1902_; lean_object* v_res_1903_; 
v_sync_boxed_1902_ = lean_unbox(v_sync_1900_);
v_res_1903_ = l_EIO_chainTask___redArg(v_t_1897_, v_f_1898_, v_prio_1899_, v_sync_boxed_1902_);
return v_res_1903_;
}
}
lean_object* l_EIO_chainTask(lean_object* v_00_u03b1_1904_, lean_object* v_00_u03b5_1905_, lean_object* v_t_1906_, lean_object* v_f_1907_, lean_object* v_prio_1908_, uint8_t v_sync_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_EIO_chainTask___redArg(v_t_1906_, v_f_1907_, v_prio_1908_, v_sync_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT void l_EIO_chainTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1906_ = stack[2].m_obj;
lean_object* v_f_1907_ = stack[3].m_obj;
lean_object* v_prio_1908_ = stack[4].m_obj;
uint8_t v_sync_1909_ = stack[5].m_num;
lean_object* v_res_1912_;
v_res_1912_ = l_EIO_chainTask(lean_box(0), lean_box(0), v_t_1906_, v_f_1907_, v_prio_1908_, v_sync_1909_);
stack->m_obj
 = v_res_1912_;
}
LEAN_EXPORT lean_object* l_EIO_chainTask___boxed(lean_object* v_00_u03b1_1913_, lean_object* v_00_u03b5_1914_, lean_object* v_t_1915_, lean_object* v_f_1916_, lean_object* v_prio_1917_, lean_object* v_sync_1918_, lean_object* v_a_1919_){
_start:
{
uint8_t v_sync_boxed_1920_; lean_object* v_res_1921_; 
v_sync_boxed_1920_ = lean_unbox(v_sync_1918_);
v_res_1921_ = l_EIO_chainTask(v_00_u03b1_1913_, v_00_u03b5_1914_, v_t_1915_, v_f_1916_, v_prio_1917_, v_sync_boxed_1920_);
return v_res_1921_;
}
}
lean_object* l_EIO_mapTasks___redArg___lam__0(lean_object* v_f_1922_, lean_object* v_as_1923_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_apply_2(v_f_1922_, v_as_1923_, lean_box(0));
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set_tag(v___x_1928_, 1);
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
v_a_1934_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1925_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1925_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 0);
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
LEAN_EXPORT void l_EIO_mapTasks___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1922_ = stack[0].m_obj;
lean_object* v_as_1923_ = stack[1].m_obj;
lean_object* v_res_1942_;
v_res_1942_ = l_EIO_mapTasks___redArg___lam__0(v_f_1922_, v_as_1923_);
stack->m_obj
 = v_res_1942_;
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___lam__0___boxed(lean_object* v_f_1943_, lean_object* v_as_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_EIO_mapTasks___redArg___lam__0(v_f_1943_, v_as_1944_);
return v_res_1946_;
}
}
lean_object* l_EIO_mapTasks___redArg(lean_object* v_f_1947_, lean_object* v_tasks_1948_, lean_object* v_prio_1949_, uint8_t v_sync_1950_){
_start:
{
lean_object* v___f_1952_; lean_object* v___x_1953_; 
v___f_1952_ = lean_alloc_closure((void*)(l_EIO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1952_, 0, v_f_1947_);
v___x_1953_ = l_BaseIO_mapTasks___redArg(v___f_1952_, v_tasks_1948_, v_prio_1949_, v_sync_1950_);
return v___x_1953_;
}
}
LEAN_EXPORT void l_EIO_mapTasks___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1947_ = stack[0].m_obj;
lean_object* v_tasks_1948_ = stack[1].m_obj;
lean_object* v_prio_1949_ = stack[2].m_obj;
uint8_t v_sync_1950_ = stack[3].m_num;
lean_object* v_res_1954_;
v_res_1954_ = l_EIO_mapTasks___redArg(v_f_1947_, v_tasks_1948_, v_prio_1949_, v_sync_1950_);
stack->m_obj
 = v_res_1954_;
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___redArg___boxed(lean_object* v_f_1955_, lean_object* v_tasks_1956_, lean_object* v_prio_1957_, lean_object* v_sync_1958_, lean_object* v_a_1959_){
_start:
{
uint8_t v_sync_boxed_1960_; lean_object* v_res_1961_; 
v_sync_boxed_1960_ = lean_unbox(v_sync_1958_);
v_res_1961_ = l_EIO_mapTasks___redArg(v_f_1955_, v_tasks_1956_, v_prio_1957_, v_sync_boxed_1960_);
return v_res_1961_;
}
}
lean_object* l_EIO_mapTasks(lean_object* v_00_u03b1_1962_, lean_object* v_00_u03b5_1963_, lean_object* v_00_u03b2_1964_, lean_object* v_f_1965_, lean_object* v_tasks_1966_, lean_object* v_prio_1967_, uint8_t v_sync_1968_){
_start:
{
lean_object* v___f_1970_; lean_object* v___x_1971_; 
v___f_1970_ = lean_alloc_closure((void*)(l_EIO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1970_, 0, v_f_1965_);
v___x_1971_ = l_BaseIO_mapTasks___redArg(v___f_1970_, v_tasks_1966_, v_prio_1967_, v_sync_1968_);
return v___x_1971_;
}
}
LEAN_EXPORT void l_EIO_mapTasks_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1965_ = stack[3].m_obj;
lean_object* v_tasks_1966_ = stack[4].m_obj;
lean_object* v_prio_1967_ = stack[5].m_obj;
uint8_t v_sync_1968_ = stack[6].m_num;
lean_object* v_res_1972_;
v_res_1972_ = l_EIO_mapTasks(lean_box(0), lean_box(0), lean_box(0), v_f_1965_, v_tasks_1966_, v_prio_1967_, v_sync_1968_);
stack->m_obj
 = v_res_1972_;
}
LEAN_EXPORT lean_object* l_EIO_mapTasks___boxed(lean_object* v_00_u03b1_1973_, lean_object* v_00_u03b5_1974_, lean_object* v_00_u03b2_1975_, lean_object* v_f_1976_, lean_object* v_tasks_1977_, lean_object* v_prio_1978_, lean_object* v_sync_1979_, lean_object* v_a_1980_){
_start:
{
uint8_t v_sync_boxed_1981_; lean_object* v_res_1982_; 
v_sync_boxed_1981_ = lean_unbox(v_sync_1979_);
v_res_1982_ = l_EIO_mapTasks(v_00_u03b1_1973_, v_00_u03b5_1974_, v_00_u03b2_1975_, v_f_1976_, v_tasks_1977_, v_prio_1978_, v_sync_boxed_1981_);
return v_res_1982_;
}
}
lean_object* l_IO_ofExcept___redArg(lean_object* v_inst_1983_, lean_object* v_e_1984_){
_start:
{
if (lean_obj_tag(v_e_1984_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1995_; 
v_a_1986_ = lean_ctor_get(v_e_1984_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_e_1984_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1988_ = v_e_1984_;
v_isShared_1989_ = v_isSharedCheck_1995_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v_e_1984_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1995_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1990_ = lean_apply_1(v_inst_1983_, v_a_1986_);
v___x_1991_ = lean_mk_io_user_error(v___x_1990_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set_tag(v___x_1988_, 1);
lean_ctor_set(v___x_1988_, 0, v___x_1991_);
v___x_1993_ = v___x_1988_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v_inst_1983_);
v_a_1996_ = lean_ctor_get(v_e_1984_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_e_1984_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v_e_1984_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v_e_1984_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set_tag(v___x_1998_, 0);
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1983_ = stack[0].m_obj;
lean_object* v_e_1984_ = stack[1].m_obj;
lean_object* v_res_2004_;
v_res_2004_ = l_IO_ofExcept___redArg(v_inst_1983_, v_e_1984_);
stack->m_obj
 = v_res_2004_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___redArg___boxed(lean_object* v_inst_2005_, lean_object* v_e_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_IO_ofExcept___redArg(v_inst_2005_, v_e_2006_);
return v_res_2008_;
}
}
lean_object* l_IO_ofExcept(lean_object* v_00_u03b5_2009_, lean_object* v_00_u03b1_2010_, lean_object* v_inst_2011_, lean_object* v_e_2012_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_IO_ofExcept___redArg(v_inst_2011_, v_e_2012_);
return v___x_2014_;
}
}
LEAN_EXPORT void l_IO_ofExcept_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2011_ = stack[2].m_obj;
lean_object* v_e_2012_ = stack[3].m_obj;
lean_object* v_res_2015_;
v_res_2015_ = l_IO_ofExcept(lean_box(0), lean_box(0), v_inst_2011_, v_e_2012_);
stack->m_obj
 = v_res_2015_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___boxed(lean_object* v_00_u03b5_2016_, lean_object* v_00_u03b1_2017_, lean_object* v_inst_2018_, lean_object* v_e_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_IO_ofExcept(v_00_u03b5_2016_, v_00_u03b1_2017_, v_inst_2018_, v_e_2019_);
return v_res_2021_;
}
}
lean_object* l_IO_lazyPure___redArg(lean_object* v_fn_2022_){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = lean_box(0);
v___x_2025_ = lean_apply_1(v_fn_2022_, v___x_2024_);
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT void l_IO_lazyPure___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_2022_ = stack[0].m_obj;
lean_object* v_res_2027_;
v_res_2027_ = l_IO_lazyPure___redArg(v_fn_2022_);
stack->m_obj
 = v_res_2027_;
}
LEAN_EXPORT lean_object* l_IO_lazyPure___redArg___boxed(lean_object* v_fn_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_IO_lazyPure___redArg(v_fn_2028_);
return v_res_2030_;
}
}
lean_object* l_IO_lazyPure(lean_object* v_00_u03b1_2031_, lean_object* v_fn_2032_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_IO_lazyPure___redArg(v_fn_2032_);
return v___x_2034_;
}
}
LEAN_EXPORT void l_IO_lazyPure_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_2032_ = stack[1].m_obj;
lean_object* v_res_2035_;
v_res_2035_ = l_IO_lazyPure(lean_box(0), v_fn_2032_);
stack->m_obj
 = v_res_2035_;
}
LEAN_EXPORT lean_object* l_IO_lazyPure___boxed(lean_object* v_00_u03b1_2036_, lean_object* v_fn_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_IO_lazyPure(v_00_u03b1_2036_, v_fn_2037_);
return v_res_2039_;
}
}
LEAN_EXPORT void l_IO_monoMsNow_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2041_;
v_res_2041_ = lean_io_mono_ms_now();
stack->m_obj
 = v_res_2041_;
}
LEAN_EXPORT lean_object* l_IO_monoMsNow___boxed(lean_object* v_a_00___x40___internal___hyg_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = lean_io_mono_ms_now();
return v_res_2043_;
}
}
LEAN_EXPORT void l_IO_monoNanosNow_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2045_;
v_res_2045_ = lean_io_mono_nanos_now();
stack->m_obj
 = v_res_2045_;
}
LEAN_EXPORT lean_object* l_IO_monoNanosNow___boxed(lean_object* v_a_00___x40___internal___hyg_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = lean_io_mono_nanos_now();
return v_res_2047_;
}
}
LEAN_EXPORT void l_IO_getRandomBytes_0interp(lean_interpreter_value* stack)
{
size_t v_nBytes_2048_ = stack[0].m_num;
lean_object* v_res_2050_;
v_res_2050_ = lean_io_get_random_bytes(v_nBytes_2048_);
stack->m_obj
 = v_res_2050_;
}
LEAN_EXPORT lean_object* l_IO_getRandomBytes___boxed(lean_object* v_nBytes_2051_, lean_object* v_a_00___x40___internal___hyg_2052_){
_start:
{
size_t v_nBytes_boxed_2053_; lean_object* v_res_2054_; 
v_nBytes_boxed_2053_ = lean_unbox_usize(v_nBytes_2051_);
lean_dec(v_nBytes_2051_);
v_res_2054_ = lean_io_get_random_bytes(v_nBytes_boxed_2053_);
return v_res_2054_;
}
}
lean_object* l_IO_sleep___lam__0(lean_object* v_x_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_box(0);
return v___x_2057_;
}
}
LEAN_EXPORT void l_IO_sleep___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2056_ = stack[0].m_obj;
lean_object* v_res_2058_;
v_res_2058_ = l_IO_sleep___lam__0(v_x_2056_);
stack->m_obj
 = v_res_2058_;
}
LEAN_EXPORT lean_object* l_IO_sleep___lam__0___boxed(lean_object* v_s_2059_, lean_object* v_x_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_IO_sleep___lam__0(v_x_2060_);
return v_res_2061_;
}
}
lean_object* l_IO_sleep(uint32_t v_ms_2062_){
_start:
{
lean_object* v___f_2064_; lean_object* v___x_2065_; 
v___f_2064_ = lean_alloc_closure((void*)(l_IO_sleep___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2064_, 0, lean_box(0));
v___x_2065_ = lean_dbg_sleep(v_ms_2062_, v___f_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT void l_IO_sleep_0interp(lean_interpreter_value* stack)
{
uint32_t v_ms_2062_ = stack[0].m_num;
lean_object* v_res_2066_;
v_res_2066_ = l_IO_sleep(v_ms_2062_);
stack->m_obj
 = v_res_2066_;
}
LEAN_EXPORT lean_object* l_IO_sleep___boxed(lean_object* v_ms_2067_, lean_object* v_s_2068_){
_start:
{
uint32_t v_ms_boxed_2069_; lean_object* v_res_2070_; 
v_ms_boxed_2069_ = lean_unbox_uint32(v_ms_2067_);
lean_dec(v_ms_2067_);
v_res_2070_ = l_IO_sleep(v_ms_boxed_2069_);
return v_res_2070_;
}
}
lean_object* l_IO_asTask___redArg(lean_object* v_act_2071_, lean_object* v_prio_2072_){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_2074_, 0, lean_box(0));
lean_closure_set(v___x_2074_, 1, lean_box(0));
lean_closure_set(v___x_2074_, 2, v_act_2071_);
v___x_2075_ = lean_io_as_task(v___x_2074_, v_prio_2072_);
return v___x_2075_;
}
}
LEAN_EXPORT void l_IO_asTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_2071_ = stack[0].m_obj;
lean_object* v_prio_2072_ = stack[1].m_obj;
lean_object* v_res_2076_;
v_res_2076_ = l_IO_asTask___redArg(v_act_2071_, v_prio_2072_);
stack->m_obj
 = v_res_2076_;
}
LEAN_EXPORT lean_object* l_IO_asTask___redArg___boxed(lean_object* v_act_2077_, lean_object* v_prio_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_IO_asTask___redArg(v_act_2077_, v_prio_2078_);
return v_res_2080_;
}
}
lean_object* l_IO_asTask(lean_object* v_00_u03b1_2081_, lean_object* v_act_2082_, lean_object* v_prio_2083_){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_2085_, 0, lean_box(0));
lean_closure_set(v___x_2085_, 1, lean_box(0));
lean_closure_set(v___x_2085_, 2, v_act_2082_);
v___x_2086_ = lean_io_as_task(v___x_2085_, v_prio_2083_);
return v___x_2086_;
}
}
LEAN_EXPORT void l_IO_asTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_2082_ = stack[1].m_obj;
lean_object* v_prio_2083_ = stack[2].m_obj;
lean_object* v_res_2087_;
v_res_2087_ = l_IO_asTask(lean_box(0), v_act_2082_, v_prio_2083_);
stack->m_obj
 = v_res_2087_;
}
LEAN_EXPORT lean_object* l_IO_asTask___boxed(lean_object* v_00_u03b1_2088_, lean_object* v_act_2089_, lean_object* v_prio_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_IO_asTask(v_00_u03b1_2088_, v_act_2089_, v_prio_2090_);
return v_res_2092_;
}
}
lean_object* l_IO_mapTask___redArg___lam__0(lean_object* v_f_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = lean_apply_2(v_f_2093_, v_a_2094_, lean_box(0));
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set_tag(v___x_2099_, 1);
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2096_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2096_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set_tag(v___x_2107_, 0);
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
LEAN_EXPORT void l_IO_mapTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2093_ = stack[0].m_obj;
lean_object* v_a_2094_ = stack[1].m_obj;
lean_object* v_res_2113_;
v_res_2113_ = l_IO_mapTask___redArg___lam__0(v_f_2093_, v_a_2094_);
stack->m_obj
 = v_res_2113_;
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___lam__0___boxed(lean_object* v_f_2114_, lean_object* v_a_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_IO_mapTask___redArg___lam__0(v_f_2114_, v_a_2115_);
return v_res_2117_;
}
}
lean_object* l_IO_mapTask___redArg(lean_object* v_f_2118_, lean_object* v_t_2119_, lean_object* v_prio_2120_, uint8_t v_sync_2121_){
_start:
{
lean_object* v___f_2123_; lean_object* v___x_2124_; 
v___f_2123_ = lean_alloc_closure((void*)(l_IO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2123_, 0, v_f_2118_);
v___x_2124_ = lean_io_map_task(v___f_2123_, v_t_2119_, v_prio_2120_, v_sync_2121_);
return v___x_2124_;
}
}
LEAN_EXPORT void l_IO_mapTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2118_ = stack[0].m_obj;
lean_object* v_t_2119_ = stack[1].m_obj;
lean_object* v_prio_2120_ = stack[2].m_obj;
uint8_t v_sync_2121_ = stack[3].m_num;
lean_object* v_res_2125_;
v_res_2125_ = l_IO_mapTask___redArg(v_f_2118_, v_t_2119_, v_prio_2120_, v_sync_2121_);
stack->m_obj
 = v_res_2125_;
}
LEAN_EXPORT lean_object* l_IO_mapTask___redArg___boxed(lean_object* v_f_2126_, lean_object* v_t_2127_, lean_object* v_prio_2128_, lean_object* v_sync_2129_, lean_object* v_a_2130_){
_start:
{
uint8_t v_sync_boxed_2131_; lean_object* v_res_2132_; 
v_sync_boxed_2131_ = lean_unbox(v_sync_2129_);
v_res_2132_ = l_IO_mapTask___redArg(v_f_2126_, v_t_2127_, v_prio_2128_, v_sync_boxed_2131_);
return v_res_2132_;
}
}
lean_object* l_IO_mapTask(lean_object* v_00_u03b1_2133_, lean_object* v_00_u03b2_2134_, lean_object* v_f_2135_, lean_object* v_t_2136_, lean_object* v_prio_2137_, uint8_t v_sync_2138_){
_start:
{
lean_object* v___f_2140_; lean_object* v___x_2141_; 
v___f_2140_ = lean_alloc_closure((void*)(l_IO_mapTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2140_, 0, v_f_2135_);
v___x_2141_ = lean_io_map_task(v___f_2140_, v_t_2136_, v_prio_2137_, v_sync_2138_);
return v___x_2141_;
}
}
LEAN_EXPORT void l_IO_mapTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2135_ = stack[2].m_obj;
lean_object* v_t_2136_ = stack[3].m_obj;
lean_object* v_prio_2137_ = stack[4].m_obj;
uint8_t v_sync_2138_ = stack[5].m_num;
lean_object* v_res_2142_;
v_res_2142_ = l_IO_mapTask(lean_box(0), lean_box(0), v_f_2135_, v_t_2136_, v_prio_2137_, v_sync_2138_);
stack->m_obj
 = v_res_2142_;
}
LEAN_EXPORT lean_object* l_IO_mapTask___boxed(lean_object* v_00_u03b1_2143_, lean_object* v_00_u03b2_2144_, lean_object* v_f_2145_, lean_object* v_t_2146_, lean_object* v_prio_2147_, lean_object* v_sync_2148_, lean_object* v_a_2149_){
_start:
{
uint8_t v_sync_boxed_2150_; lean_object* v_res_2151_; 
v_sync_boxed_2150_ = lean_unbox(v_sync_2148_);
v_res_2151_ = l_IO_mapTask(v_00_u03b1_2143_, v_00_u03b2_2144_, v_f_2145_, v_t_2146_, v_prio_2147_, v_sync_boxed_2150_);
return v_res_2151_;
}
}
lean_object* l_IO_bindTask___redArg___lam__0(lean_object* v_f_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_apply_2(v_f_2152_, v_a_2153_, lean_box(0));
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2155_, 1);
return v_a_2156_;
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2165_; 
v_a_2157_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2159_ = v___x_2155_;
v_isShared_2160_ = v_isSharedCheck_2165_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2155_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2165_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
lean_ctor_set_tag(v___x_2159_, 0);
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_task_pure(v___x_2162_);
return v___x_2163_;
}
}
}
}
}
LEAN_EXPORT void l_IO_bindTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2152_ = stack[0].m_obj;
lean_object* v_a_2153_ = stack[1].m_obj;
lean_object* v_res_2166_;
v_res_2166_ = l_IO_bindTask___redArg___lam__0(v_f_2152_, v_a_2153_);
stack->m_obj
 = v_res_2166_;
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___lam__0___boxed(lean_object* v_f_2167_, lean_object* v_a_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_IO_bindTask___redArg___lam__0(v_f_2167_, v_a_2168_);
return v_res_2170_;
}
}
lean_object* l_IO_bindTask___redArg(lean_object* v_t_2171_, lean_object* v_f_2172_, lean_object* v_prio_2173_, uint8_t v_sync_2174_){
_start:
{
lean_object* v___f_2176_; lean_object* v___x_2177_; 
v___f_2176_ = lean_alloc_closure((void*)(l_IO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2176_, 0, v_f_2172_);
v___x_2177_ = lean_io_bind_task(v_t_2171_, v___f_2176_, v_prio_2173_, v_sync_2174_);
return v___x_2177_;
}
}
LEAN_EXPORT void l_IO_bindTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2171_ = stack[0].m_obj;
lean_object* v_f_2172_ = stack[1].m_obj;
lean_object* v_prio_2173_ = stack[2].m_obj;
uint8_t v_sync_2174_ = stack[3].m_num;
lean_object* v_res_2178_;
v_res_2178_ = l_IO_bindTask___redArg(v_t_2171_, v_f_2172_, v_prio_2173_, v_sync_2174_);
stack->m_obj
 = v_res_2178_;
}
LEAN_EXPORT lean_object* l_IO_bindTask___redArg___boxed(lean_object* v_t_2179_, lean_object* v_f_2180_, lean_object* v_prio_2181_, lean_object* v_sync_2182_, lean_object* v_a_2183_){
_start:
{
uint8_t v_sync_boxed_2184_; lean_object* v_res_2185_; 
v_sync_boxed_2184_ = lean_unbox(v_sync_2182_);
v_res_2185_ = l_IO_bindTask___redArg(v_t_2179_, v_f_2180_, v_prio_2181_, v_sync_boxed_2184_);
return v_res_2185_;
}
}
lean_object* l_IO_bindTask(lean_object* v_00_u03b1_2186_, lean_object* v_00_u03b2_2187_, lean_object* v_t_2188_, lean_object* v_f_2189_, lean_object* v_prio_2190_, uint8_t v_sync_2191_){
_start:
{
lean_object* v___f_2193_; lean_object* v___x_2194_; 
v___f_2193_ = lean_alloc_closure((void*)(l_IO_bindTask___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2193_, 0, v_f_2189_);
v___x_2194_ = lean_io_bind_task(v_t_2188_, v___f_2193_, v_prio_2190_, v_sync_2191_);
return v___x_2194_;
}
}
LEAN_EXPORT void l_IO_bindTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2188_ = stack[2].m_obj;
lean_object* v_f_2189_ = stack[3].m_obj;
lean_object* v_prio_2190_ = stack[4].m_obj;
uint8_t v_sync_2191_ = stack[5].m_num;
lean_object* v_res_2195_;
v_res_2195_ = l_IO_bindTask(lean_box(0), lean_box(0), v_t_2188_, v_f_2189_, v_prio_2190_, v_sync_2191_);
stack->m_obj
 = v_res_2195_;
}
LEAN_EXPORT lean_object* l_IO_bindTask___boxed(lean_object* v_00_u03b1_2196_, lean_object* v_00_u03b2_2197_, lean_object* v_t_2198_, lean_object* v_f_2199_, lean_object* v_prio_2200_, lean_object* v_sync_2201_, lean_object* v_a_2202_){
_start:
{
uint8_t v_sync_boxed_2203_; lean_object* v_res_2204_; 
v_sync_boxed_2203_ = lean_unbox(v_sync_2201_);
v_res_2204_ = l_IO_bindTask(v_00_u03b1_2196_, v_00_u03b2_2197_, v_t_2198_, v_f_2199_, v_prio_2200_, v_sync_boxed_2203_);
return v_res_2204_;
}
}
lean_object* l_IO_chainTask___redArg(lean_object* v_t_2205_, lean_object* v_f_2206_, lean_object* v_prio_2207_, uint8_t v_sync_2208_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_EIO_chainTask___redArg(v_t_2205_, v_f_2206_, v_prio_2207_, v_sync_2208_);
return v___x_2210_;
}
}
LEAN_EXPORT void l_IO_chainTask___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2205_ = stack[0].m_obj;
lean_object* v_f_2206_ = stack[1].m_obj;
lean_object* v_prio_2207_ = stack[2].m_obj;
uint8_t v_sync_2208_ = stack[3].m_num;
lean_object* v_res_2211_;
v_res_2211_ = l_IO_chainTask___redArg(v_t_2205_, v_f_2206_, v_prio_2207_, v_sync_2208_);
stack->m_obj
 = v_res_2211_;
}
LEAN_EXPORT lean_object* l_IO_chainTask___redArg___boxed(lean_object* v_t_2212_, lean_object* v_f_2213_, lean_object* v_prio_2214_, lean_object* v_sync_2215_, lean_object* v_a_2216_){
_start:
{
uint8_t v_sync_boxed_2217_; lean_object* v_res_2218_; 
v_sync_boxed_2217_ = lean_unbox(v_sync_2215_);
v_res_2218_ = l_IO_chainTask___redArg(v_t_2212_, v_f_2213_, v_prio_2214_, v_sync_boxed_2217_);
return v_res_2218_;
}
}
lean_object* l_IO_chainTask(lean_object* v_00_u03b1_2219_, lean_object* v_t_2220_, lean_object* v_f_2221_, lean_object* v_prio_2222_, uint8_t v_sync_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_EIO_chainTask___redArg(v_t_2220_, v_f_2221_, v_prio_2222_, v_sync_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT void l_IO_chainTask_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2220_ = stack[1].m_obj;
lean_object* v_f_2221_ = stack[2].m_obj;
lean_object* v_prio_2222_ = stack[3].m_obj;
uint8_t v_sync_2223_ = stack[4].m_num;
lean_object* v_res_2226_;
v_res_2226_ = l_IO_chainTask(lean_box(0), v_t_2220_, v_f_2221_, v_prio_2222_, v_sync_2223_);
stack->m_obj
 = v_res_2226_;
}
LEAN_EXPORT lean_object* l_IO_chainTask___boxed(lean_object* v_00_u03b1_2227_, lean_object* v_t_2228_, lean_object* v_f_2229_, lean_object* v_prio_2230_, lean_object* v_sync_2231_, lean_object* v_a_2232_){
_start:
{
uint8_t v_sync_boxed_2233_; lean_object* v_res_2234_; 
v_sync_boxed_2233_ = lean_unbox(v_sync_2231_);
v_res_2234_ = l_IO_chainTask(v_00_u03b1_2227_, v_t_2228_, v_f_2229_, v_prio_2230_, v_sync_boxed_2233_);
return v_res_2234_;
}
}
lean_object* l_IO_mapTasks___redArg___lam__0(lean_object* v_f_2235_, lean_object* v_as_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = lean_apply_2(v_f_2235_, v_as_2236_, lean_box(0));
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set_tag(v___x_2241_, 1);
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_a_2247_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2238_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2238_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
lean_ctor_set_tag(v___x_2249_, 0);
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
LEAN_EXPORT void l_IO_mapTasks___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2235_ = stack[0].m_obj;
lean_object* v_as_2236_ = stack[1].m_obj;
lean_object* v_res_2255_;
v_res_2255_ = l_IO_mapTasks___redArg___lam__0(v_f_2235_, v_as_2236_);
stack->m_obj
 = v_res_2255_;
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___lam__0___boxed(lean_object* v_f_2256_, lean_object* v_as_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_IO_mapTasks___redArg___lam__0(v_f_2256_, v_as_2257_);
return v_res_2259_;
}
}
lean_object* l_IO_mapTasks___redArg(lean_object* v_f_2260_, lean_object* v_tasks_2261_, lean_object* v_prio_2262_, uint8_t v_sync_2263_){
_start:
{
lean_object* v___f_2265_; lean_object* v___x_2266_; 
v___f_2265_ = lean_alloc_closure((void*)(l_IO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2265_, 0, v_f_2260_);
v___x_2266_ = l_BaseIO_mapTasks___redArg(v___f_2265_, v_tasks_2261_, v_prio_2262_, v_sync_2263_);
return v___x_2266_;
}
}
LEAN_EXPORT void l_IO_mapTasks___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2260_ = stack[0].m_obj;
lean_object* v_tasks_2261_ = stack[1].m_obj;
lean_object* v_prio_2262_ = stack[2].m_obj;
uint8_t v_sync_2263_ = stack[3].m_num;
lean_object* v_res_2267_;
v_res_2267_ = l_IO_mapTasks___redArg(v_f_2260_, v_tasks_2261_, v_prio_2262_, v_sync_2263_);
stack->m_obj
 = v_res_2267_;
}
LEAN_EXPORT lean_object* l_IO_mapTasks___redArg___boxed(lean_object* v_f_2268_, lean_object* v_tasks_2269_, lean_object* v_prio_2270_, lean_object* v_sync_2271_, lean_object* v_a_2272_){
_start:
{
uint8_t v_sync_boxed_2273_; lean_object* v_res_2274_; 
v_sync_boxed_2273_ = lean_unbox(v_sync_2271_);
v_res_2274_ = l_IO_mapTasks___redArg(v_f_2268_, v_tasks_2269_, v_prio_2270_, v_sync_boxed_2273_);
return v_res_2274_;
}
}
lean_object* l_IO_mapTasks(lean_object* v_00_u03b1_2275_, lean_object* v_00_u03b2_2276_, lean_object* v_f_2277_, lean_object* v_tasks_2278_, lean_object* v_prio_2279_, uint8_t v_sync_2280_){
_start:
{
lean_object* v___f_2282_; lean_object* v___x_2283_; 
v___f_2282_ = lean_alloc_closure((void*)(l_IO_mapTasks___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2282_, 0, v_f_2277_);
v___x_2283_ = l_BaseIO_mapTasks___redArg(v___f_2282_, v_tasks_2278_, v_prio_2279_, v_sync_2280_);
return v___x_2283_;
}
}
LEAN_EXPORT void l_IO_mapTasks_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2277_ = stack[2].m_obj;
lean_object* v_tasks_2278_ = stack[3].m_obj;
lean_object* v_prio_2279_ = stack[4].m_obj;
uint8_t v_sync_2280_ = stack[5].m_num;
lean_object* v_res_2284_;
v_res_2284_ = l_IO_mapTasks(lean_box(0), lean_box(0), v_f_2277_, v_tasks_2278_, v_prio_2279_, v_sync_2280_);
stack->m_obj
 = v_res_2284_;
}
LEAN_EXPORT lean_object* l_IO_mapTasks___boxed(lean_object* v_00_u03b1_2285_, lean_object* v_00_u03b2_2286_, lean_object* v_f_2287_, lean_object* v_tasks_2288_, lean_object* v_prio_2289_, lean_object* v_sync_2290_, lean_object* v_a_2291_){
_start:
{
uint8_t v_sync_boxed_2292_; lean_object* v_res_2293_; 
v_sync_boxed_2292_ = lean_unbox(v_sync_2290_);
v_res_2293_ = l_IO_mapTasks(v_00_u03b1_2285_, v_00_u03b2_2286_, v_f_2287_, v_tasks_2288_, v_prio_2289_, v_sync_boxed_2292_);
return v_res_2293_;
}
}
LEAN_EXPORT void l_IO_checkCanceled_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_2295_;
v_res_2295_ = lean_io_check_canceled();
stack->m_num = v_res_2295_;
}
LEAN_EXPORT lean_object* l_IO_checkCanceled___boxed(lean_object* v_a_00___x40___internal___hyg_2296_){
_start:
{
uint8_t v_res_2297_; lean_object* v_r_2298_; 
v_res_2297_ = lean_io_check_canceled();
v_r_2298_ = lean_box(v_res_2297_);
return v_r_2298_;
}
}
LEAN_EXPORT void l_IO_cancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_2300_ = stack[1].m_obj;
lean_object* v_res_2302_;
v_res_2302_ = lean_io_cancel(v_a_00___x40___internal___hyg_2300_);
stack->m_obj
 = v_res_2302_;
}
LEAN_EXPORT lean_object* l_IO_cancel___boxed(lean_object* v_00_u03b1_2303_, lean_object* v_a_00___x40___internal___hyg_2304_, lean_object* v_a_00___x40___internal___hyg_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = lean_io_cancel(v_a_00___x40___internal___hyg_2304_);
lean_dec_ref(v_a_00___x40___internal___hyg_2304_);
return v_res_2306_;
}
}
lean_object* l_IO_TaskState_ctorIdx___impl(uint8_t v_x_2307_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_box(v_x_2307_);
v___x_2309_ = lean_obj_tag_nat(v___x_2308_);
lean_dec(v___x_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT void l_IO_TaskState_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2307_ = stack[0].m_num;
lean_object* v_res_2310_;
v_res_2310_ = l_IO_TaskState_ctorIdx___impl(v_x_2307_);
stack->m_obj
 = v_res_2310_;
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorIdx___impl___boxed(lean_object* v_x_2311_){
_start:
{
uint8_t v_x_4__boxed_2312_; lean_object* v_res_2313_; 
v_x_4__boxed_2312_ = lean_unbox(v_x_2311_);
v_res_2313_ = l_IO_TaskState_ctorIdx___impl(v_x_4__boxed_2312_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg(lean_object* v_k_2314_){
_start:
{
lean_inc(v_k_2314_);
return v_k_2314_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___redArg___boxed(lean_object* v_k_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_IO_TaskState_ctorElim___redArg(v_k_2315_);
lean_dec(v_k_2315_);
return v_res_2316_;
}
}
lean_object* l_IO_TaskState_ctorElim(lean_object* v_motive_2317_, lean_object* v_ctorIdx_2318_, uint8_t v_t_2319_, lean_object* v_h_2320_, lean_object* v_k_2321_){
_start:
{
lean_inc(v_k_2321_);
return v_k_2321_;
}
}
LEAN_EXPORT void l_IO_TaskState_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_2318_ = stack[1].m_obj;
uint8_t v_t_2319_ = stack[2].m_num;
lean_object* v_k_2321_ = stack[4].m_obj;
lean_object* v_res_2322_;
v_res_2322_ = l_IO_TaskState_ctorElim(lean_box(0), v_ctorIdx_2318_, v_t_2319_, lean_box(0), v_k_2321_);
stack->m_obj
 = v_res_2322_;
}
LEAN_EXPORT lean_object* l_IO_TaskState_ctorElim___boxed(lean_object* v_motive_2323_, lean_object* v_ctorIdx_2324_, lean_object* v_t_2325_, lean_object* v_h_2326_, lean_object* v_k_2327_){
_start:
{
uint8_t v_t_boxed_2328_; lean_object* v_res_2329_; 
v_t_boxed_2328_ = lean_unbox(v_t_2325_);
v_res_2329_ = l_IO_TaskState_ctorElim(v_motive_2323_, v_ctorIdx_2324_, v_t_boxed_2328_, v_h_2326_, v_k_2327_);
lean_dec(v_k_2327_);
lean_dec(v_ctorIdx_2324_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg(lean_object* v_waiting_2330_){
_start:
{
lean_inc(v_waiting_2330_);
return v_waiting_2330_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___redArg___boxed(lean_object* v_waiting_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_IO_TaskState_waiting_elim___redArg(v_waiting_2331_);
lean_dec(v_waiting_2331_);
return v_res_2332_;
}
}
lean_object* l_IO_TaskState_waiting_elim(lean_object* v_motive_2333_, uint8_t v_t_2334_, lean_object* v_h_2335_, lean_object* v_waiting_2336_){
_start:
{
lean_inc(v_waiting_2336_);
return v_waiting_2336_;
}
}
LEAN_EXPORT void l_IO_TaskState_waiting_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2334_ = stack[1].m_num;
lean_object* v_waiting_2336_ = stack[3].m_obj;
lean_object* v_res_2337_;
v_res_2337_ = l_IO_TaskState_waiting_elim(lean_box(0), v_t_2334_, lean_box(0), v_waiting_2336_);
stack->m_obj
 = v_res_2337_;
}
LEAN_EXPORT lean_object* l_IO_TaskState_waiting_elim___boxed(lean_object* v_motive_2338_, lean_object* v_t_2339_, lean_object* v_h_2340_, lean_object* v_waiting_2341_){
_start:
{
uint8_t v_t_boxed_2342_; lean_object* v_res_2343_; 
v_t_boxed_2342_ = lean_unbox(v_t_2339_);
v_res_2343_ = l_IO_TaskState_waiting_elim(v_motive_2338_, v_t_boxed_2342_, v_h_2340_, v_waiting_2341_);
lean_dec(v_waiting_2341_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg(lean_object* v_running_2344_){
_start:
{
lean_inc(v_running_2344_);
return v_running_2344_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___redArg___boxed(lean_object* v_running_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_IO_TaskState_running_elim___redArg(v_running_2345_);
lean_dec(v_running_2345_);
return v_res_2346_;
}
}
lean_object* l_IO_TaskState_running_elim(lean_object* v_motive_2347_, uint8_t v_t_2348_, lean_object* v_h_2349_, lean_object* v_running_2350_){
_start:
{
lean_inc(v_running_2350_);
return v_running_2350_;
}
}
LEAN_EXPORT void l_IO_TaskState_running_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2348_ = stack[1].m_num;
lean_object* v_running_2350_ = stack[3].m_obj;
lean_object* v_res_2351_;
v_res_2351_ = l_IO_TaskState_running_elim(lean_box(0), v_t_2348_, lean_box(0), v_running_2350_);
stack->m_obj
 = v_res_2351_;
}
LEAN_EXPORT lean_object* l_IO_TaskState_running_elim___boxed(lean_object* v_motive_2352_, lean_object* v_t_2353_, lean_object* v_h_2354_, lean_object* v_running_2355_){
_start:
{
uint8_t v_t_boxed_2356_; lean_object* v_res_2357_; 
v_t_boxed_2356_ = lean_unbox(v_t_2353_);
v_res_2357_ = l_IO_TaskState_running_elim(v_motive_2352_, v_t_boxed_2356_, v_h_2354_, v_running_2355_);
lean_dec(v_running_2355_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg(lean_object* v_finished_2358_){
_start:
{
lean_inc(v_finished_2358_);
return v_finished_2358_;
}
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___redArg___boxed(lean_object* v_finished_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_IO_TaskState_finished_elim___redArg(v_finished_2359_);
lean_dec(v_finished_2359_);
return v_res_2360_;
}
}
lean_object* l_IO_TaskState_finished_elim(lean_object* v_motive_2361_, uint8_t v_t_2362_, lean_object* v_h_2363_, lean_object* v_finished_2364_){
_start:
{
lean_inc(v_finished_2364_);
return v_finished_2364_;
}
}
LEAN_EXPORT void l_IO_TaskState_finished_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2362_ = stack[1].m_num;
lean_object* v_finished_2364_ = stack[3].m_obj;
lean_object* v_res_2365_;
v_res_2365_ = l_IO_TaskState_finished_elim(lean_box(0), v_t_2362_, lean_box(0), v_finished_2364_);
stack->m_obj
 = v_res_2365_;
}
LEAN_EXPORT lean_object* l_IO_TaskState_finished_elim___boxed(lean_object* v_motive_2366_, lean_object* v_t_2367_, lean_object* v_h_2368_, lean_object* v_finished_2369_){
_start:
{
uint8_t v_t_boxed_2370_; lean_object* v_res_2371_; 
v_t_boxed_2370_ = lean_unbox(v_t_2367_);
v_res_2371_ = l_IO_TaskState_finished_elim(v_motive_2366_, v_t_boxed_2370_, v_h_2368_, v_finished_2369_);
lean_dec(v_finished_2369_);
return v_res_2371_;
}
}
static uint8_t _init_l_IO_instInhabitedTaskState_default(void){
_start:
{
uint8_t v___x_2372_; 
v___x_2372_ = 0;
return v___x_2372_;
}
}
static uint8_t _init_l_IO_instInhabitedTaskState(void){
_start:
{
uint8_t v___x_2373_; 
v___x_2373_ = 0;
return v___x_2373_;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__6(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = lean_unsigned_to_nat(2u);
v___x_2384_ = lean_nat_to_int(v___x_2383_);
return v___x_2384_;
}
}
static lean_object* _init_l_IO_instReprTaskState_repr___closed__7(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_unsigned_to_nat(1u);
v___x_2386_ = lean_nat_to_int(v___x_2385_);
return v___x_2386_;
}
}
lean_object* l_IO_instReprTaskState_repr(uint8_t v_x_2387_, lean_object* v_prec_2388_){
_start:
{
lean_object* v___y_2390_; lean_object* v___y_2397_; lean_object* v___y_2404_; 
switch(v_x_2387_)
{
case 0:
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = lean_unsigned_to_nat(1024u);
v___x_2411_ = lean_nat_dec_le(v___x_2410_, v_prec_2388_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2390_ = v___x_2412_;
goto v___jp_2389_;
}
else
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2390_ = v___x_2413_;
goto v___jp_2389_;
}
}
case 1:
{
lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2414_ = lean_unsigned_to_nat(1024u);
v___x_2415_ = lean_nat_dec_le(v___x_2414_, v_prec_2388_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2397_ = v___x_2416_;
goto v___jp_2396_;
}
else
{
lean_object* v___x_2417_; 
v___x_2417_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2397_ = v___x_2417_;
goto v___jp_2396_;
}
}
default: 
{
lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2418_ = lean_unsigned_to_nat(1024u);
v___x_2419_ = lean_nat_dec_le(v___x_2418_, v_prec_2388_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_2404_ = v___x_2420_;
goto v___jp_2403_;
}
else
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_2404_ = v___x_2421_;
goto v___jp_2403_;
}
}
}
v___jp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2391_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__1));
lean_inc(v___y_2390_);
v___x_2392_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___y_2390_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = 0;
v___x_2394_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*1, v___x_2393_);
v___x_2395_ = l_Repr_addAppParen(v___x_2394_, v_prec_2388_);
return v___x_2395_;
}
v___jp_2396_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2398_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__3));
lean_inc(v___y_2397_);
v___x_2399_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___y_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = 0;
v___x_2401_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set_uint8(v___x_2401_, sizeof(void*)*1, v___x_2400_);
v___x_2402_ = l_Repr_addAppParen(v___x_2401_, v_prec_2388_);
return v___x_2402_;
}
v___jp_2403_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2405_ = ((lean_object*)(l_IO_instReprTaskState_repr___closed__5));
lean_inc(v___y_2404_);
v___x_2406_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___y_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = 0;
v___x_2408_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2408_, 0, v___x_2406_);
lean_ctor_set_uint8(v___x_2408_, sizeof(void*)*1, v___x_2407_);
v___x_2409_ = l_Repr_addAppParen(v___x_2408_, v_prec_2388_);
return v___x_2409_;
}
}
}
LEAN_EXPORT void l_IO_instReprTaskState_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2387_ = stack[0].m_num;
lean_object* v_prec_2388_ = stack[1].m_obj;
lean_object* v_res_2422_;
v_res_2422_ = l_IO_instReprTaskState_repr(v_x_2387_, v_prec_2388_);
stack->m_obj
 = v_res_2422_;
}
LEAN_EXPORT lean_object* l_IO_instReprTaskState_repr___boxed(lean_object* v_x_2423_, lean_object* v_prec_2424_){
_start:
{
uint8_t v_x_171__boxed_2425_; lean_object* v_res_2426_; 
v_x_171__boxed_2425_ = lean_unbox(v_x_2423_);
v_res_2426_ = l_IO_instReprTaskState_repr(v_x_171__boxed_2425_, v_prec_2424_);
lean_dec(v_prec_2424_);
return v_res_2426_;
}
}
uint8_t l_IO_TaskState_ofNat(lean_object* v_n_2429_){
_start:
{
lean_object* v___x_2430_; uint8_t v___x_2431_; 
v___x_2430_ = lean_unsigned_to_nat(0u);
v___x_2431_ = lean_nat_dec_le(v_n_2429_, v___x_2430_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2432_ = lean_unsigned_to_nat(1u);
v___x_2433_ = lean_nat_dec_le(v_n_2429_, v___x_2432_);
if (v___x_2433_ == 0)
{
uint8_t v___x_2434_; 
v___x_2434_ = 2;
return v___x_2434_;
}
else
{
uint8_t v___x_2435_; 
v___x_2435_ = 1;
return v___x_2435_;
}
}
else
{
uint8_t v___x_2436_; 
v___x_2436_ = 0;
return v___x_2436_;
}
}
}
LEAN_EXPORT void l_IO_TaskState_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2429_ = stack[0].m_obj;
uint8_t v_res_2437_;
v_res_2437_ = l_IO_TaskState_ofNat(v_n_2429_);
stack->m_num = v_res_2437_;
}
LEAN_EXPORT lean_object* l_IO_TaskState_ofNat___boxed(lean_object* v_n_2438_){
_start:
{
uint8_t v_res_2439_; lean_object* v_r_2440_; 
v_res_2439_ = l_IO_TaskState_ofNat(v_n_2438_);
lean_dec(v_n_2438_);
v_r_2440_ = lean_box(v_res_2439_);
return v_r_2440_;
}
}
uint8_t l_IO_instDecidableEqTaskState(uint8_t v_x_2441_, uint8_t v_y_2442_){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2443_ = lean_box(v_x_2441_);
v___x_2444_ = lean_obj_tag_nat(v___x_2443_);
lean_dec(v___x_2443_);
v___x_2445_ = lean_box(v_y_2442_);
v___x_2446_ = lean_obj_tag_nat(v___x_2445_);
lean_dec(v___x_2445_);
v___x_2447_ = lean_nat_dec_eq(v___x_2444_, v___x_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT void l_IO_instDecidableEqTaskState_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2441_ = stack[0].m_num;
uint8_t v_y_2442_ = stack[1].m_num;
uint8_t v_res_2448_;
v_res_2448_ = l_IO_instDecidableEqTaskState(v_x_2441_, v_y_2442_);
stack->m_num = v_res_2448_;
}
LEAN_EXPORT lean_object* l_IO_instDecidableEqTaskState___boxed(lean_object* v_x_2449_, lean_object* v_y_2450_){
_start:
{
uint8_t v_x_23__boxed_2451_; uint8_t v_y_24__boxed_2452_; uint8_t v_res_2453_; lean_object* v_r_2454_; 
v_x_23__boxed_2451_ = lean_unbox(v_x_2449_);
v_y_24__boxed_2452_ = lean_unbox(v_y_2450_);
v_res_2453_ = l_IO_instDecidableEqTaskState(v_x_23__boxed_2451_, v_y_24__boxed_2452_);
v_r_2454_ = lean_box(v_res_2453_);
return v_r_2454_;
}
}
uint8_t l_IO_instOrdTaskState_ord(uint8_t v_x_2455_, uint8_t v_y_2456_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2457_ = lean_box(v_x_2455_);
v___x_2458_ = lean_obj_tag_nat(v___x_2457_);
lean_dec(v___x_2457_);
v___x_2459_ = lean_box(v_y_2456_);
v___x_2460_ = lean_obj_tag_nat(v___x_2459_);
lean_dec(v___x_2459_);
v___x_2461_ = lean_nat_dec_lt(v___x_2458_, v___x_2460_);
if (v___x_2461_ == 0)
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_nat_dec_eq(v___x_2458_, v___x_2460_);
if (v___x_2462_ == 0)
{
uint8_t v___x_2463_; 
v___x_2463_ = 2;
return v___x_2463_;
}
else
{
uint8_t v___x_2464_; 
v___x_2464_ = 1;
return v___x_2464_;
}
}
else
{
uint8_t v___x_2465_; 
v___x_2465_ = 0;
return v___x_2465_;
}
}
}
LEAN_EXPORT void l_IO_instOrdTaskState_ord_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2455_ = stack[0].m_num;
uint8_t v_y_2456_ = stack[1].m_num;
uint8_t v_res_2466_;
v_res_2466_ = l_IO_instOrdTaskState_ord(v_x_2455_, v_y_2456_);
stack->m_num = v_res_2466_;
}
LEAN_EXPORT lean_object* l_IO_instOrdTaskState_ord___boxed(lean_object* v_x_2467_, lean_object* v_y_2468_){
_start:
{
uint8_t v_x_33__boxed_2469_; uint8_t v_y_34__boxed_2470_; uint8_t v_res_2471_; lean_object* v_r_2472_; 
v_x_33__boxed_2469_ = lean_unbox(v_x_2467_);
v_y_34__boxed_2470_ = lean_unbox(v_y_2468_);
v_res_2471_ = l_IO_instOrdTaskState_ord(v_x_33__boxed_2469_, v_y_34__boxed_2470_);
v_r_2472_ = lean_box(v_res_2471_);
return v_r_2472_;
}
}
static lean_object* _init_l_IO_instLTTaskState(void){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_box(0);
return v___x_2475_;
}
}
static lean_object* _init_l_IO_instLETaskState(void){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_box(0);
return v___x_2476_;
}
}
uint8_t l_IO_instMinTaskState___lam__0(uint8_t v_x_2477_, uint8_t v_y_2478_){
_start:
{
uint8_t v___x_2479_; 
v___x_2479_ = l_IO_instOrdTaskState_ord(v_x_2477_, v_y_2478_);
if (v___x_2479_ == 2)
{
return v_y_2478_;
}
else
{
return v_x_2477_;
}
}
}
LEAN_EXPORT void l_IO_instMinTaskState___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2477_ = stack[0].m_num;
uint8_t v_y_2478_ = stack[1].m_num;
uint8_t v_res_2480_;
v_res_2480_ = l_IO_instMinTaskState___lam__0(v_x_2477_, v_y_2478_);
stack->m_num = v_res_2480_;
}
LEAN_EXPORT lean_object* l_IO_instMinTaskState___lam__0___boxed(lean_object* v_x_2481_, lean_object* v_y_2482_){
_start:
{
uint8_t v_x_boxed_2483_; uint8_t v_y_boxed_2484_; uint8_t v_res_2485_; lean_object* v_r_2486_; 
v_x_boxed_2483_ = lean_unbox(v_x_2481_);
v_y_boxed_2484_ = lean_unbox(v_y_2482_);
v_res_2485_ = l_IO_instMinTaskState___lam__0(v_x_boxed_2483_, v_y_boxed_2484_);
v_r_2486_ = lean_box(v_res_2485_);
return v_r_2486_;
}
}
uint8_t l_IO_instMaxTaskState___lam__0(uint8_t v_x_2489_, uint8_t v_y_2490_){
_start:
{
uint8_t v___x_2491_; 
v___x_2491_ = l_IO_instOrdTaskState_ord(v_x_2489_, v_y_2490_);
if (v___x_2491_ == 2)
{
return v_x_2489_;
}
else
{
return v_y_2490_;
}
}
}
LEAN_EXPORT void l_IO_instMaxTaskState___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2489_ = stack[0].m_num;
uint8_t v_y_2490_ = stack[1].m_num;
uint8_t v_res_2492_;
v_res_2492_ = l_IO_instMaxTaskState___lam__0(v_x_2489_, v_y_2490_);
stack->m_num = v_res_2492_;
}
LEAN_EXPORT lean_object* l_IO_instMaxTaskState___lam__0___boxed(lean_object* v_x_2493_, lean_object* v_y_2494_){
_start:
{
uint8_t v_x_boxed_2495_; uint8_t v_y_boxed_2496_; uint8_t v_res_2497_; lean_object* v_r_2498_; 
v_x_boxed_2495_ = lean_unbox(v_x_2493_);
v_y_boxed_2496_ = lean_unbox(v_y_2494_);
v_res_2497_ = l_IO_instMaxTaskState___lam__0(v_x_boxed_2495_, v_y_boxed_2496_);
v_r_2498_ = lean_box(v_res_2497_);
return v_r_2498_;
}
}
lean_object* l_IO_TaskState_toString(uint8_t v_x_2504_){
_start:
{
switch(v_x_2504_)
{
case 0:
{
lean_object* v___x_2505_; 
v___x_2505_ = ((lean_object*)(l_IO_TaskState_toString___closed__0));
return v___x_2505_;
}
case 1:
{
lean_object* v___x_2506_; 
v___x_2506_ = ((lean_object*)(l_IO_TaskState_toString___closed__1));
return v___x_2506_;
}
default: 
{
lean_object* v___x_2507_; 
v___x_2507_ = ((lean_object*)(l_IO_TaskState_toString___closed__2));
return v___x_2507_;
}
}
}
}
LEAN_EXPORT void l_IO_TaskState_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2504_ = stack[0].m_num;
lean_object* v_res_2508_;
v_res_2508_ = l_IO_TaskState_toString(v_x_2504_);
stack->m_obj
 = v_res_2508_;
}
LEAN_EXPORT lean_object* l_IO_TaskState_toString___boxed(lean_object* v_x_2509_){
_start:
{
uint8_t v_x_31__boxed_2510_; lean_object* v_res_2511_; 
v_x_31__boxed_2510_ = lean_unbox(v_x_2509_);
v_res_2511_ = l_IO_TaskState_toString(v_x_31__boxed_2510_);
return v_res_2511_;
}
}
LEAN_EXPORT void l_IO_getTaskState_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_2515_ = stack[1].m_obj;
uint8_t v_res_2517_;
v_res_2517_ = lean_io_get_task_state(v_a_00___x40___internal___hyg_2515_);
stack->m_num = v_res_2517_;
}
LEAN_EXPORT lean_object* l_IO_getTaskState___boxed(lean_object* v_00_u03b1_2518_, lean_object* v_a_00___x40___internal___hyg_2519_, lean_object* v_a_00___x40___internal___hyg_2520_){
_start:
{
uint8_t v_res_2521_; lean_object* v_r_2522_; 
v_res_2521_ = lean_io_get_task_state(v_a_00___x40___internal___hyg_2519_);
lean_dec_ref(v_a_00___x40___internal___hyg_2519_);
v_r_2522_ = lean_box(v_res_2521_);
return v_r_2522_;
}
}
uint8_t l_IO_hasFinished___redArg(lean_object* v_task_2523_){
_start:
{
uint8_t v___x_2525_; 
v___x_2525_ = lean_io_get_task_state(v_task_2523_);
if (v___x_2525_ == 2)
{
uint8_t v___x_2526_; 
v___x_2526_ = 1;
return v___x_2526_;
}
else
{
uint8_t v___x_2527_; 
v___x_2527_ = 0;
return v___x_2527_;
}
}
}
LEAN_EXPORT void l_IO_hasFinished___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_task_2523_ = stack[0].m_obj;
uint8_t v_res_2528_;
v_res_2528_ = l_IO_hasFinished___redArg(v_task_2523_);
stack->m_num = v_res_2528_;
}
LEAN_EXPORT lean_object* l_IO_hasFinished___redArg___boxed(lean_object* v_task_2529_, lean_object* v_a_2530_){
_start:
{
uint8_t v_res_2531_; lean_object* v_r_2532_; 
v_res_2531_ = l_IO_hasFinished___redArg(v_task_2529_);
lean_dec_ref(v_task_2529_);
v_r_2532_ = lean_box(v_res_2531_);
return v_r_2532_;
}
}
uint8_t l_IO_hasFinished(lean_object* v_00_u03b1_2533_, lean_object* v_task_2534_){
_start:
{
uint8_t v___x_2536_; 
v___x_2536_ = lean_io_get_task_state(v_task_2534_);
if (v___x_2536_ == 2)
{
uint8_t v___x_2537_; 
v___x_2537_ = 1;
return v___x_2537_;
}
else
{
uint8_t v___x_2538_; 
v___x_2538_ = 0;
return v___x_2538_;
}
}
}
LEAN_EXPORT void l_IO_hasFinished_0interp(lean_interpreter_value* stack)
{
lean_object* v_task_2534_ = stack[1].m_obj;
uint8_t v_res_2539_;
v_res_2539_ = l_IO_hasFinished(lean_box(0), v_task_2534_);
stack->m_num = v_res_2539_;
}
LEAN_EXPORT lean_object* l_IO_hasFinished___boxed(lean_object* v_00_u03b1_2540_, lean_object* v_task_2541_, lean_object* v_a_2542_){
_start:
{
uint8_t v_res_2543_; lean_object* v_r_2544_; 
v_res_2543_ = l_IO_hasFinished(v_00_u03b1_2540_, v_task_2541_);
lean_dec_ref(v_task_2541_);
v_r_2544_ = lean_box(v_res_2543_);
return v_r_2544_;
}
}
LEAN_EXPORT void l_IO_wait_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2546_ = stack[1].m_obj;
lean_object* v_res_2548_;
v_res_2548_ = lean_io_wait(v_t_2546_);
stack->m_obj
 = v_res_2548_;
}
LEAN_EXPORT lean_object* l_IO_wait___boxed(lean_object* v_00_u03b1_2549_, lean_object* v_t_2550_, lean_object* v_a_00___x40___internal___hyg_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = lean_io_wait(v_t_2550_);
return v_res_2552_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__10));
v___x_2580_ = l_Lean_mkAtom(v___x_2579_);
return v___x_2580_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__12, &l_IO_waitAny___auto__1___closed__12_once, _init_l_IO_waitAny___auto__1___closed__12);
v___x_2582_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2583_ = lean_array_push(v___x_2582_, v___x_2581_);
return v___x_2583_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__22));
v___x_2607_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2608_ = lean_array_push(v___x_2607_, v___x_2606_);
return v___x_2608_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__27(void){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__26));
v___x_2617_ = l_Lean_mkAtom(v___x_2616_);
return v___x_2617_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__28(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__27, &l_IO_waitAny___auto__1___closed__27_once, _init_l_IO_waitAny___auto__1___closed__27);
v___x_2619_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2620_ = lean_array_push(v___x_2619_, v___x_2618_);
return v___x_2620_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__29(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2621_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__28, &l_IO_waitAny___auto__1___closed__28_once, _init_l_IO_waitAny___auto__1___closed__28);
v___x_2622_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__25));
v___x_2623_ = lean_box(2);
v___x_2624_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v___x_2622_);
lean_ctor_set(v___x_2624_, 2, v___x_2621_);
return v___x_2624_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__30(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2625_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__29, &l_IO_waitAny___auto__1___closed__29_once, _init_l_IO_waitAny___auto__1___closed__29);
v___x_2626_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2627_ = lean_array_push(v___x_2626_, v___x_2625_);
return v___x_2627_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__31(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2628_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__30, &l_IO_waitAny___auto__1___closed__30_once, _init_l_IO_waitAny___auto__1___closed__30);
v___x_2629_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_2630_ = lean_box(2);
v___x_2631_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
lean_ctor_set(v___x_2631_, 1, v___x_2629_);
lean_ctor_set(v___x_2631_, 2, v___x_2628_);
return v___x_2631_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__32(void){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2632_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__31, &l_IO_waitAny___auto__1___closed__31_once, _init_l_IO_waitAny___auto__1___closed__31);
v___x_2633_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__23, &l_IO_waitAny___auto__1___closed__23_once, _init_l_IO_waitAny___auto__1___closed__23);
v___x_2634_ = lean_array_push(v___x_2633_, v___x_2632_);
return v___x_2634_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__33(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2635_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__32, &l_IO_waitAny___auto__1___closed__32_once, _init_l_IO_waitAny___auto__1___closed__32);
v___x_2636_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_2637_ = lean_box(2);
v___x_2638_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
lean_ctor_set(v___x_2638_, 1, v___x_2636_);
lean_ctor_set(v___x_2638_, 2, v___x_2635_);
return v___x_2638_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__34(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__33, &l_IO_waitAny___auto__1___closed__33_once, _init_l_IO_waitAny___auto__1___closed__33);
v___x_2640_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__13, &l_IO_waitAny___auto__1___closed__13_once, _init_l_IO_waitAny___auto__1___closed__13);
v___x_2641_ = lean_array_push(v___x_2640_, v___x_2639_);
return v___x_2641_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__35(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2642_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__34, &l_IO_waitAny___auto__1___closed__34_once, _init_l_IO_waitAny___auto__1___closed__34);
v___x_2643_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__11));
v___x_2644_ = lean_box(2);
v___x_2645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
lean_ctor_set(v___x_2645_, 1, v___x_2643_);
lean_ctor_set(v___x_2645_, 2, v___x_2642_);
return v___x_2645_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__36(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2646_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__35, &l_IO_waitAny___auto__1___closed__35_once, _init_l_IO_waitAny___auto__1___closed__35);
v___x_2647_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2648_ = lean_array_push(v___x_2647_, v___x_2646_);
return v___x_2648_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__37(void){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2649_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__36, &l_IO_waitAny___auto__1___closed__36_once, _init_l_IO_waitAny___auto__1___closed__36);
v___x_2650_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_2651_ = lean_box(2);
v___x_2652_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
lean_ctor_set(v___x_2652_, 1, v___x_2650_);
lean_ctor_set(v___x_2652_, 2, v___x_2649_);
return v___x_2652_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__38(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__37, &l_IO_waitAny___auto__1___closed__37_once, _init_l_IO_waitAny___auto__1___closed__37);
v___x_2654_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2655_ = lean_array_push(v___x_2654_, v___x_2653_);
return v___x_2655_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__39(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2656_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__38, &l_IO_waitAny___auto__1___closed__38_once, _init_l_IO_waitAny___auto__1___closed__38);
v___x_2657_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__7));
v___x_2658_ = lean_box(2);
v___x_2659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
lean_ctor_set(v___x_2659_, 1, v___x_2657_);
lean_ctor_set(v___x_2659_, 2, v___x_2656_);
return v___x_2659_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__40(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__39, &l_IO_waitAny___auto__1___closed__39_once, _init_l_IO_waitAny___auto__1___closed__39);
v___x_2661_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__5));
v___x_2662_ = lean_array_push(v___x_2661_, v___x_2660_);
return v___x_2662_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1___closed__41(void){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2663_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__40, &l_IO_waitAny___auto__1___closed__40_once, _init_l_IO_waitAny___auto__1___closed__40);
v___x_2664_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__4));
v___x_2665_ = lean_box(2);
v___x_2666_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
lean_ctor_set(v___x_2666_, 1, v___x_2664_);
lean_ctor_set(v___x_2666_, 2, v___x_2663_);
return v___x_2666_;
}
}
static lean_object* _init_l_IO_waitAny___auto__1(void){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__41, &l_IO_waitAny___auto__1___closed__41_once, _init_l_IO_waitAny___auto__1___closed__41);
return v___x_2667_;
}
}
LEAN_EXPORT void l_IO_waitAny_0interp(lean_interpreter_value* stack)
{
lean_object* v_tasks_2669_ = stack[1].m_obj;
lean_object* v_res_2672_;
v_res_2672_ = lean_io_wait_any(v_tasks_2669_);
stack->m_obj
 = v_res_2672_;
}
LEAN_EXPORT lean_object* l_IO_waitAny___boxed(lean_object* v_00_u03b1_2673_, lean_object* v_tasks_2674_, lean_object* v_h_2675_, lean_object* v_a_00___x40___internal___hyg_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = lean_io_wait_any(v_tasks_2674_);
lean_dec(v_tasks_2674_);
return v_res_2677_;
}
}
static lean_object* _init_l_IO_waitAny_x27___auto__1(void){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_obj_once(&l_IO_waitAny___auto__1___closed__41, &l_IO_waitAny___auto__1___closed__41_once, _init_l_IO_waitAny___auto__1___closed__41);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0(lean_object* v___x_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2679_);
lean_ctor_set(v___x_2681_, 1, v_a_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
if (lean_obj_tag(v_a_2682_) == 0)
{
lean_object* v___x_2684_; 
v___x_2684_ = lean_array_to_list(v_a_2683_);
return v___x_2684_;
}
else
{
lean_object* v_head_2685_; lean_object* v_tail_2686_; lean_object* v___x_2687_; lean_object* v___f_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_head_2685_ = lean_ctor_get(v_a_2682_, 0);
lean_inc(v_head_2685_);
v_tail_2686_ = lean_ctor_get(v_a_2682_, 1);
lean_inc(v_tail_2686_);
lean_dec_ref_known(v_a_2682_, 2);
v___x_2687_ = lean_array_get_size(v_a_2683_);
v___f_2688_ = lean_alloc_closure((void*)(l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2688_, 0, v___x_2687_);
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = 1;
v___x_2691_ = lean_task_map(v___f_2688_, v_head_2685_, v___x_2689_, v___x_2690_);
v___x_2692_ = lean_array_push(v_a_2683_, v___x_2691_);
v_a_2682_ = v_tail_2686_;
v_a_2683_ = v___x_2692_;
goto _start;
}
}
}
lean_object* l_IO_waitAny_x27___redArg(lean_object* v_tasks_2696_){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v_fst_2701_; lean_object* v_snd_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2710_; 
v___x_2698_ = ((lean_object*)(l_IO_waitAny_x27___redArg___closed__0));
lean_inc(v_tasks_2696_);
v___x_2699_ = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(v_tasks_2696_, v___x_2698_);
v___x_2700_ = lean_io_wait_any(v___x_2699_);
lean_dec(v___x_2699_);
v_fst_2701_ = lean_ctor_get(v___x_2700_, 0);
v_snd_2702_ = lean_ctor_get(v___x_2700_, 1);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2704_ = v___x_2700_;
v_isShared_2705_ = v_isSharedCheck_2710_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_snd_2702_);
lean_inc(v_fst_2701_);
lean_dec(v___x_2700_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2710_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2706_; lean_object* v___x_2708_; 
lean_inc(v_tasks_2696_);
v___x_2706_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_box(0), v_tasks_2696_, v_tasks_2696_, v_fst_2701_, v___x_2698_);
lean_dec(v_tasks_2696_);
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 1, v___x_2706_);
lean_ctor_set(v___x_2704_, 0, v_snd_2702_);
v___x_2708_ = v___x_2704_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_snd_2702_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
LEAN_EXPORT void l_IO_waitAny_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tasks_2696_ = stack[0].m_obj;
lean_object* v_res_2711_;
v_res_2711_ = l_IO_waitAny_x27___redArg(v_tasks_2696_);
stack->m_obj
 = v_res_2711_;
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___redArg___boxed(lean_object* v_tasks_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_IO_waitAny_x27___redArg(v_tasks_2712_);
return v_res_2714_;
}
}
lean_object* l_IO_waitAny_x27(lean_object* v_00_u03b1_2715_, lean_object* v_tasks_2716_, lean_object* v_h_2717_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_IO_waitAny_x27___redArg(v_tasks_2716_);
return v___x_2719_;
}
}
LEAN_EXPORT void l_IO_waitAny_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_tasks_2716_ = stack[1].m_obj;
lean_object* v_res_2720_;
v_res_2720_ = l_IO_waitAny_x27(lean_box(0), v_tasks_2716_, lean_box(0));
stack->m_obj
 = v_res_2720_;
}
LEAN_EXPORT lean_object* l_IO_waitAny_x27___boxed(lean_object* v_00_u03b1_2721_, lean_object* v_tasks_2722_, lean_object* v_h_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_IO_waitAny_x27(v_00_u03b1_2721_, v_tasks_2722_, v_h_2723_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0(lean_object* v_00_u03b1_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_List_mapIdx_go___at___00IO_waitAny_x27_spec__0___redArg(v_a_2727_, v_a_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT void l_IO_getNumHeartbeats_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2731_;
v_res_2731_ = lean_io_get_num_heartbeats();
stack->m_obj
 = v_res_2731_;
}
LEAN_EXPORT lean_object* l_IO_getNumHeartbeats___boxed(lean_object* v_a_00___x40___internal___hyg_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = lean_io_get_num_heartbeats();
return v_res_2733_;
}
}
LEAN_EXPORT void l_IO_setNumHeartbeats_0interp(lean_interpreter_value* stack)
{
lean_object* v_count_2734_ = stack[0].m_obj;
lean_object* v_res_2736_;
v_res_2736_ = lean_io_set_heartbeats(v_count_2734_);
stack->m_obj
 = v_res_2736_;
}
LEAN_EXPORT lean_object* l_IO_setNumHeartbeats___boxed(lean_object* v_count_2737_, lean_object* v_a_00___x40___internal___hyg_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = lean_io_set_heartbeats(v_count_2737_);
return v_res_2739_;
}
}
lean_object* l_IO_addHeartbeats(lean_object* v_count_2740_){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2742_ = lean_io_get_num_heartbeats();
v___x_2743_ = lean_nat_add(v___x_2742_, v_count_2740_);
lean_dec(v___x_2742_);
v___x_2744_ = lean_io_set_heartbeats(v___x_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT void l_IO_addHeartbeats_0interp(lean_interpreter_value* stack)
{
lean_object* v_count_2740_ = stack[0].m_obj;
lean_object* v_res_2745_;
v_res_2745_ = l_IO_addHeartbeats(v_count_2740_);
stack->m_obj
 = v_res_2745_;
}
LEAN_EXPORT lean_object* l_IO_addHeartbeats___boxed(lean_object* v_count_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_IO_addHeartbeats(v_count_2746_);
lean_dec(v_count_2746_);
return v_res_2748_;
}
}
lean_object* l_IO_FS_Mode_ctorIdx___impl(uint8_t v_x_2749_){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = lean_box(v_x_2749_);
v___x_2751_ = lean_obj_tag_nat(v___x_2750_);
lean_dec(v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT void l_IO_FS_Mode_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2749_ = stack[0].m_num;
lean_object* v_res_2752_;
v_res_2752_ = l_IO_FS_Mode_ctorIdx___impl(v_x_2749_);
stack->m_obj
 = v_res_2752_;
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorIdx___impl___boxed(lean_object* v_x_2753_){
_start:
{
uint8_t v_x_4__boxed_2754_; lean_object* v_res_2755_; 
v_x_4__boxed_2754_ = lean_unbox(v_x_2753_);
v_res_2755_ = l_IO_FS_Mode_ctorIdx___impl(v_x_4__boxed_2754_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg(lean_object* v_k_2756_){
_start:
{
lean_inc(v_k_2756_);
return v_k_2756_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___redArg___boxed(lean_object* v_k_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_IO_FS_Mode_ctorElim___redArg(v_k_2757_);
lean_dec(v_k_2757_);
return v_res_2758_;
}
}
lean_object* l_IO_FS_Mode_ctorElim(lean_object* v_motive_2759_, lean_object* v_ctorIdx_2760_, uint8_t v_t_2761_, lean_object* v_h_2762_, lean_object* v_k_2763_){
_start:
{
lean_inc(v_k_2763_);
return v_k_2763_;
}
}
LEAN_EXPORT void l_IO_FS_Mode_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_2760_ = stack[1].m_obj;
uint8_t v_t_2761_ = stack[2].m_num;
lean_object* v_k_2763_ = stack[4].m_obj;
lean_object* v_res_2764_;
v_res_2764_ = l_IO_FS_Mode_ctorElim(lean_box(0), v_ctorIdx_2760_, v_t_2761_, lean_box(0), v_k_2763_);
stack->m_obj
 = v_res_2764_;
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_ctorElim___boxed(lean_object* v_motive_2765_, lean_object* v_ctorIdx_2766_, lean_object* v_t_2767_, lean_object* v_h_2768_, lean_object* v_k_2769_){
_start:
{
uint8_t v_t_boxed_2770_; lean_object* v_res_2771_; 
v_t_boxed_2770_ = lean_unbox(v_t_2767_);
v_res_2771_ = l_IO_FS_Mode_ctorElim(v_motive_2765_, v_ctorIdx_2766_, v_t_boxed_2770_, v_h_2768_, v_k_2769_);
lean_dec(v_k_2769_);
lean_dec(v_ctorIdx_2766_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg(lean_object* v_read_2772_){
_start:
{
lean_inc(v_read_2772_);
return v_read_2772_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___redArg___boxed(lean_object* v_read_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_IO_FS_Mode_read_elim___redArg(v_read_2773_);
lean_dec(v_read_2773_);
return v_res_2774_;
}
}
lean_object* l_IO_FS_Mode_read_elim(lean_object* v_motive_2775_, uint8_t v_t_2776_, lean_object* v_h_2777_, lean_object* v_read_2778_){
_start:
{
lean_inc(v_read_2778_);
return v_read_2778_;
}
}
LEAN_EXPORT void l_IO_FS_Mode_read_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2776_ = stack[1].m_num;
lean_object* v_read_2778_ = stack[3].m_obj;
lean_object* v_res_2779_;
v_res_2779_ = l_IO_FS_Mode_read_elim(lean_box(0), v_t_2776_, lean_box(0), v_read_2778_);
stack->m_obj
 = v_res_2779_;
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_read_elim___boxed(lean_object* v_motive_2780_, lean_object* v_t_2781_, lean_object* v_h_2782_, lean_object* v_read_2783_){
_start:
{
uint8_t v_t_boxed_2784_; lean_object* v_res_2785_; 
v_t_boxed_2784_ = lean_unbox(v_t_2781_);
v_res_2785_ = l_IO_FS_Mode_read_elim(v_motive_2780_, v_t_boxed_2784_, v_h_2782_, v_read_2783_);
lean_dec(v_read_2783_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg(lean_object* v_write_2786_){
_start:
{
lean_inc(v_write_2786_);
return v_write_2786_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___redArg___boxed(lean_object* v_write_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_IO_FS_Mode_write_elim___redArg(v_write_2787_);
lean_dec(v_write_2787_);
return v_res_2788_;
}
}
lean_object* l_IO_FS_Mode_write_elim(lean_object* v_motive_2789_, uint8_t v_t_2790_, lean_object* v_h_2791_, lean_object* v_write_2792_){
_start:
{
lean_inc(v_write_2792_);
return v_write_2792_;
}
}
LEAN_EXPORT void l_IO_FS_Mode_write_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2790_ = stack[1].m_num;
lean_object* v_write_2792_ = stack[3].m_obj;
lean_object* v_res_2793_;
v_res_2793_ = l_IO_FS_Mode_write_elim(lean_box(0), v_t_2790_, lean_box(0), v_write_2792_);
stack->m_obj
 = v_res_2793_;
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_write_elim___boxed(lean_object* v_motive_2794_, lean_object* v_t_2795_, lean_object* v_h_2796_, lean_object* v_write_2797_){
_start:
{
uint8_t v_t_boxed_2798_; lean_object* v_res_2799_; 
v_t_boxed_2798_ = lean_unbox(v_t_2795_);
v_res_2799_ = l_IO_FS_Mode_write_elim(v_motive_2794_, v_t_boxed_2798_, v_h_2796_, v_write_2797_);
lean_dec(v_write_2797_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg(lean_object* v_writeNew_2800_){
_start:
{
lean_inc(v_writeNew_2800_);
return v_writeNew_2800_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___redArg___boxed(lean_object* v_writeNew_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_IO_FS_Mode_writeNew_elim___redArg(v_writeNew_2801_);
lean_dec(v_writeNew_2801_);
return v_res_2802_;
}
}
lean_object* l_IO_FS_Mode_writeNew_elim(lean_object* v_motive_2803_, uint8_t v_t_2804_, lean_object* v_h_2805_, lean_object* v_writeNew_2806_){
_start:
{
lean_inc(v_writeNew_2806_);
return v_writeNew_2806_;
}
}
LEAN_EXPORT void l_IO_FS_Mode_writeNew_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2804_ = stack[1].m_num;
lean_object* v_writeNew_2806_ = stack[3].m_obj;
lean_object* v_res_2807_;
v_res_2807_ = l_IO_FS_Mode_writeNew_elim(lean_box(0), v_t_2804_, lean_box(0), v_writeNew_2806_);
stack->m_obj
 = v_res_2807_;
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_writeNew_elim___boxed(lean_object* v_motive_2808_, lean_object* v_t_2809_, lean_object* v_h_2810_, lean_object* v_writeNew_2811_){
_start:
{
uint8_t v_t_boxed_2812_; lean_object* v_res_2813_; 
v_t_boxed_2812_ = lean_unbox(v_t_2809_);
v_res_2813_ = l_IO_FS_Mode_writeNew_elim(v_motive_2808_, v_t_boxed_2812_, v_h_2810_, v_writeNew_2811_);
lean_dec(v_writeNew_2811_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg(lean_object* v_readWrite_2814_){
_start:
{
lean_inc(v_readWrite_2814_);
return v_readWrite_2814_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___redArg___boxed(lean_object* v_readWrite_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_IO_FS_Mode_readWrite_elim___redArg(v_readWrite_2815_);
lean_dec(v_readWrite_2815_);
return v_res_2816_;
}
}
lean_object* l_IO_FS_Mode_readWrite_elim(lean_object* v_motive_2817_, uint8_t v_t_2818_, lean_object* v_h_2819_, lean_object* v_readWrite_2820_){
_start:
{
lean_inc(v_readWrite_2820_);
return v_readWrite_2820_;
}
}
LEAN_EXPORT void l_IO_FS_Mode_readWrite_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2818_ = stack[1].m_num;
lean_object* v_readWrite_2820_ = stack[3].m_obj;
lean_object* v_res_2821_;
v_res_2821_ = l_IO_FS_Mode_readWrite_elim(lean_box(0), v_t_2818_, lean_box(0), v_readWrite_2820_);
stack->m_obj
 = v_res_2821_;
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_readWrite_elim___boxed(lean_object* v_motive_2822_, lean_object* v_t_2823_, lean_object* v_h_2824_, lean_object* v_readWrite_2825_){
_start:
{
uint8_t v_t_boxed_2826_; lean_object* v_res_2827_; 
v_t_boxed_2826_ = lean_unbox(v_t_2823_);
v_res_2827_ = l_IO_FS_Mode_readWrite_elim(v_motive_2822_, v_t_boxed_2826_, v_h_2824_, v_readWrite_2825_);
lean_dec(v_readWrite_2825_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg(lean_object* v_append_2828_){
_start:
{
lean_inc(v_append_2828_);
return v_append_2828_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___redArg___boxed(lean_object* v_append_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_IO_FS_Mode_append_elim___redArg(v_append_2829_);
lean_dec(v_append_2829_);
return v_res_2830_;
}
}
lean_object* l_IO_FS_Mode_append_elim(lean_object* v_motive_2831_, uint8_t v_t_2832_, lean_object* v_h_2833_, lean_object* v_append_2834_){
_start:
{
lean_inc(v_append_2834_);
return v_append_2834_;
}
}
LEAN_EXPORT void l_IO_FS_Mode_append_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2832_ = stack[1].m_num;
lean_object* v_append_2834_ = stack[3].m_obj;
lean_object* v_res_2835_;
v_res_2835_ = l_IO_FS_Mode_append_elim(lean_box(0), v_t_2832_, lean_box(0), v_append_2834_);
stack->m_obj
 = v_res_2835_;
}
LEAN_EXPORT lean_object* l_IO_FS_Mode_append_elim___boxed(lean_object* v_motive_2836_, lean_object* v_t_2837_, lean_object* v_h_2838_, lean_object* v_append_2839_){
_start:
{
uint8_t v_t_boxed_2840_; lean_object* v_res_2841_; 
v_t_boxed_2840_ = lean_unbox(v_t_2837_);
v_res_2841_ = l_IO_FS_Mode_append_elim(v_motive_2836_, v_t_boxed_2840_, v_h_2838_, v_append_2839_);
lean_dec(v_append_2839_);
return v_res_2841_;
}
}
lean_object* l_IO_FS_instInhabitedStream_default___lam__0(){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT void l_IO_FS_instInhabitedStream_default___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2848_;
v_res_2848_ = l_IO_FS_instInhabitedStream_default___lam__0();
stack->m_obj
 = v_res_2848_;
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__0___boxed(lean_object* v___y_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_IO_FS_instInhabitedStream_default___lam__0();
return v_res_2850_;
}
}
lean_object* l_IO_FS_instInhabitedStream_default___lam__1(){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT void l_IO_FS_instInhabitedStream_default___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2854_;
v_res_2854_ = l_IO_FS_instInhabitedStream_default___lam__1();
stack->m_obj
 = v_res_2854_;
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__1___boxed(lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_IO_FS_instInhabitedStream_default___lam__1();
return v_res_2856_;
}
}
lean_object* l_IO_FS_instInhabitedStream_default___lam__2(lean_object* v_x_2857_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT void l_IO_FS_instInhabitedStream_default___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2857_ = stack[0].m_obj;
lean_object* v_res_2861_;
v_res_2861_ = l_IO_FS_instInhabitedStream_default___lam__2(v_x_2857_);
stack->m_obj
 = v_res_2861_;
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__2___boxed(lean_object* v_x_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_IO_FS_instInhabitedStream_default___lam__2(v_x_2862_);
lean_dec_ref(v_x_2862_);
return v_res_2864_;
}
}
lean_object* l_IO_FS_instInhabitedStream_default___lam__3(lean_object* v_x_2865_){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT void l_IO_FS_instInhabitedStream_default___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2865_ = stack[0].m_obj;
lean_object* v_res_2869_;
v_res_2869_ = l_IO_FS_instInhabitedStream_default___lam__3(v_x_2865_);
stack->m_obj
 = v_res_2869_;
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__3___boxed(lean_object* v_x_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_IO_FS_instInhabitedStream_default___lam__3(v_x_2870_);
lean_dec_ref(v_x_2870_);
return v_res_2872_;
}
}
lean_object* l_IO_FS_instInhabitedStream_default___lam__4(size_t v_x_2873_){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___lam__0___closed__1));
v___x_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT void l_IO_FS_instInhabitedStream_default___lam__4_0interp(lean_interpreter_value* stack)
{
size_t v_x_2873_ = stack[0].m_num;
lean_object* v_res_2877_;
v_res_2877_ = l_IO_FS_instInhabitedStream_default___lam__4(v_x_2873_);
stack->m_obj
 = v_res_2877_;
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__4___boxed(lean_object* v_x_2878_, lean_object* v___y_2879_){
_start:
{
size_t v_x_216__boxed_2880_; lean_object* v_res_2881_; 
v_x_216__boxed_2880_ = lean_unbox_usize(v_x_2878_);
lean_dec(v_x_2878_);
v_res_2881_ = l_IO_FS_instInhabitedStream_default___lam__4(v_x_216__boxed_2880_);
return v_res_2881_;
}
}
uint8_t l_IO_FS_instInhabitedStream_default___lam__5(uint8_t v___x_2882_){
_start:
{
return v___x_2882_;
}
}
LEAN_EXPORT void l_IO_FS_instInhabitedStream_default___lam__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2882_ = stack[0].m_num;
uint8_t v_res_2884_;
v_res_2884_ = l_IO_FS_instInhabitedStream_default___lam__5(v___x_2882_);
stack->m_num = v_res_2884_;
}
LEAN_EXPORT lean_object* l_IO_FS_instInhabitedStream_default___lam__5___boxed(lean_object* v___x_2885_, lean_object* v___y_2886_){
_start:
{
uint8_t v___x_233__boxed_2887_; uint8_t v_res_2888_; lean_object* v_r_2889_; 
v___x_233__boxed_2887_ = lean_unbox(v___x_2885_);
v_res_2888_ = l_IO_FS_instInhabitedStream_default___lam__5(v___x_233__boxed_2887_);
v_r_2889_ = lean_box(v_res_2888_);
return v_r_2889_;
}
}
LEAN_EXPORT void l_IO_getStdin_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2908_;
v_res_2908_ = lean_get_stdin();
stack->m_obj
 = v_res_2908_;
}
LEAN_EXPORT lean_object* l_IO_getStdin___boxed(lean_object* v_a_00___x40___internal___hyg_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = lean_get_stdin();
return v_res_2910_;
}
}
LEAN_EXPORT void l_IO_getStdout_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2912_;
v_res_2912_ = lean_get_stdout();
stack->m_obj
 = v_res_2912_;
}
LEAN_EXPORT lean_object* l_IO_getStdout___boxed(lean_object* v_a_00___x40___internal___hyg_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = lean_get_stdout();
return v_res_2914_;
}
}
LEAN_EXPORT void l_IO_getStderr_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2916_;
v_res_2916_ = lean_get_stderr();
stack->m_obj
 = v_res_2916_;
}
LEAN_EXPORT lean_object* l_IO_getStderr___boxed(lean_object* v_a_00___x40___internal___hyg_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = lean_get_stderr();
return v_res_2918_;
}
}
LEAN_EXPORT void l_IO_setStdin_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_2919_ = stack[0].m_obj;
lean_object* v_res_2921_;
v_res_2921_ = lean_get_set_stdin(v_a_00___x40___internal___hyg_2919_);
stack->m_obj
 = v_res_2921_;
}
LEAN_EXPORT lean_object* l_IO_setStdin___boxed(lean_object* v_a_00___x40___internal___hyg_2922_, lean_object* v_a_00___x40___internal___hyg_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = lean_get_set_stdin(v_a_00___x40___internal___hyg_2922_);
return v_res_2924_;
}
}
LEAN_EXPORT void l_IO_setStdout_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_2925_ = stack[0].m_obj;
lean_object* v_res_2927_;
v_res_2927_ = lean_get_set_stdout(v_a_00___x40___internal___hyg_2925_);
stack->m_obj
 = v_res_2927_;
}
LEAN_EXPORT lean_object* l_IO_setStdout___boxed(lean_object* v_a_00___x40___internal___hyg_2928_, lean_object* v_a_00___x40___internal___hyg_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = lean_get_set_stdout(v_a_00___x40___internal___hyg_2928_);
return v_res_2930_;
}
}
LEAN_EXPORT void l_IO_setStderr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_2931_ = stack[0].m_obj;
lean_object* v_res_2933_;
v_res_2933_ = lean_get_set_stderr(v_a_00___x40___internal___hyg_2931_);
stack->m_obj
 = v_res_2933_;
}
LEAN_EXPORT lean_object* l_IO_setStderr___boxed(lean_object* v_a_00___x40___internal___hyg_2934_, lean_object* v_a_00___x40___internal___hyg_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = lean_get_set_stderr(v_a_00___x40___internal___hyg_2934_);
return v_res_2936_;
}
}
lean_object* l_IO_iterate___redArg(lean_object* v_a_2937_, lean_object* v_f_2938_){
_start:
{
lean_object* v___x_2940_; 
lean_inc_ref(v_f_2938_);
v___x_2940_ = lean_apply_2(v_f_2938_, v_a_2937_, lean_box(0));
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2951_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2951_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2951_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
if (lean_obj_tag(v_a_2941_) == 0)
{
lean_object* v_val_2945_; 
lean_del_object(v___x_2943_);
v_val_2945_ = lean_ctor_get(v_a_2941_, 0);
lean_inc(v_val_2945_);
lean_dec_ref_known(v_a_2941_, 1);
v_a_2937_ = v_val_2945_;
goto _start;
}
else
{
lean_object* v_val_2947_; lean_object* v___x_2949_; 
lean_dec_ref(v_f_2938_);
v_val_2947_ = lean_ctor_get(v_a_2941_, 0);
lean_inc(v_val_2947_);
lean_dec_ref_known(v_a_2941_, 1);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v_val_2947_);
v___x_2949_ = v___x_2943_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_val_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec_ref(v_f_2938_);
v_a_2952_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2940_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2940_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
LEAN_EXPORT void l_IO_iterate___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2937_ = stack[0].m_obj;
lean_object* v_f_2938_ = stack[1].m_obj;
lean_object* v_res_2960_;
v_res_2960_ = l_IO_iterate___redArg(v_a_2937_, v_f_2938_);
stack->m_obj
 = v_res_2960_;
}
LEAN_EXPORT lean_object* l_IO_iterate___redArg___boxed(lean_object* v_a_2961_, lean_object* v_f_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_IO_iterate___redArg(v_a_2961_, v_f_2962_);
return v_res_2964_;
}
}
lean_object* l_IO_iterate(lean_object* v_00_u03b1_2965_, lean_object* v_00_u03b2_2966_, lean_object* v_a_2967_, lean_object* v_f_2968_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_IO_iterate___redArg(v_a_2967_, v_f_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT void l_IO_iterate_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2967_ = stack[2].m_obj;
lean_object* v_f_2968_ = stack[3].m_obj;
lean_object* v_res_2971_;
v_res_2971_ = l_IO_iterate(lean_box(0), lean_box(0), v_a_2967_, v_f_2968_);
stack->m_obj
 = v_res_2971_;
}
LEAN_EXPORT lean_object* l_IO_iterate___boxed(lean_object* v_00_u03b1_2972_, lean_object* v_00_u03b2_2973_, lean_object* v_a_2974_, lean_object* v_f_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_IO_iterate(v_00_u03b1_2972_, v_00_u03b2_2973_, v_a_2974_, v_f_2975_);
return v_res_2977_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_2978_ = stack[0].m_obj;
uint8_t v_mode_2979_ = stack[1].m_num;
lean_object* v_res_2981_;
v_res_2981_ = lean_io_prim_handle_mk(v_fn_2978_, v_mode_2979_);
stack->m_obj
 = v_res_2981_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_mk___boxed(lean_object* v_fn_2982_, lean_object* v_mode_2983_, lean_object* v_a_00___x40___internal___hyg_2984_){
_start:
{
uint8_t v_mode_boxed_2985_; lean_object* v_res_2986_; 
v_mode_boxed_2985_ = lean_unbox(v_mode_2983_);
v_res_2986_ = lean_io_prim_handle_mk(v_fn_2982_, v_mode_boxed_2985_);
lean_dec_ref(v_fn_2982_);
return v_res_2986_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_lock_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_2987_ = stack[0].m_obj;
uint8_t v_exclusive_2988_ = stack[1].m_num;
lean_object* v_res_2990_;
v_res_2990_ = lean_io_prim_handle_lock(v_h_2987_, v_exclusive_2988_);
stack->m_obj
 = v_res_2990_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lock___boxed(lean_object* v_h_2991_, lean_object* v_exclusive_2992_, lean_object* v_a_00___x40___internal___hyg_2993_){
_start:
{
uint8_t v_exclusive_boxed_2994_; lean_object* v_res_2995_; 
v_exclusive_boxed_2994_ = lean_unbox(v_exclusive_2992_);
v_res_2995_ = lean_io_prim_handle_lock(v_h_2991_, v_exclusive_boxed_2994_);
lean_dec(v_h_2991_);
return v_res_2995_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_tryLock_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_2996_ = stack[0].m_obj;
uint8_t v_exclusive_2997_ = stack[1].m_num;
lean_object* v_res_2999_;
v_res_2999_ = lean_io_prim_handle_try_lock(v_h_2996_, v_exclusive_2997_);
stack->m_obj
 = v_res_2999_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_tryLock___boxed(lean_object* v_h_3000_, lean_object* v_exclusive_3001_, lean_object* v_a_00___x40___internal___hyg_3002_){
_start:
{
uint8_t v_exclusive_boxed_3003_; lean_object* v_res_3004_; 
v_exclusive_boxed_3003_ = lean_unbox(v_exclusive_3001_);
v_res_3004_ = lean_io_prim_handle_try_lock(v_h_3000_, v_exclusive_boxed_3003_);
lean_dec(v_h_3000_);
return v_res_3004_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_unlock_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3005_ = stack[0].m_obj;
lean_object* v_res_3007_;
v_res_3007_ = lean_io_prim_handle_unlock(v_h_3005_);
stack->m_obj
 = v_res_3007_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_unlock___boxed(lean_object* v_h_3008_, lean_object* v_a_00___x40___internal___hyg_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = lean_io_prim_handle_unlock(v_h_3008_);
lean_dec(v_h_3008_);
return v_res_3010_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_isTty_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3011_ = stack[0].m_obj;
uint8_t v_res_3013_;
v_res_3013_ = lean_io_prim_handle_is_tty(v_h_3011_);
stack->m_num = v_res_3013_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_isTty___boxed(lean_object* v_h_3014_, lean_object* v_a_00___x40___internal___hyg_3015_){
_start:
{
uint8_t v_res_3016_; lean_object* v_r_3017_; 
v_res_3016_ = lean_io_prim_handle_is_tty(v_h_3014_);
lean_dec(v_h_3014_);
v_r_3017_ = lean_box(v_res_3016_);
return v_r_3017_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_flush_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3018_ = stack[0].m_obj;
lean_object* v_res_3020_;
v_res_3020_ = lean_io_prim_handle_flush(v_h_3018_);
stack->m_obj
 = v_res_3020_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_flush___boxed(lean_object* v_h_3021_, lean_object* v_a_00___x40___internal___hyg_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = lean_io_prim_handle_flush(v_h_3021_);
lean_dec(v_h_3021_);
return v_res_3023_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_rewind_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3024_ = stack[0].m_obj;
lean_object* v_res_3026_;
v_res_3026_ = lean_io_prim_handle_rewind(v_h_3024_);
stack->m_obj
 = v_res_3026_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_rewind___boxed(lean_object* v_h_3027_, lean_object* v_a_00___x40___internal___hyg_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = lean_io_prim_handle_rewind(v_h_3027_);
lean_dec(v_h_3027_);
return v_res_3029_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_truncate_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3030_ = stack[0].m_obj;
lean_object* v_res_3032_;
v_res_3032_ = lean_io_prim_handle_truncate(v_h_3030_);
stack->m_obj
 = v_res_3032_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_truncate___boxed(lean_object* v_h_3033_, lean_object* v_a_00___x40___internal___hyg_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = lean_io_prim_handle_truncate(v_h_3033_);
lean_dec(v_h_3033_);
return v_res_3035_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_read_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3036_ = stack[0].m_obj;
size_t v_bytes_3037_ = stack[1].m_num;
lean_object* v_res_3039_;
v_res_3039_ = lean_io_prim_handle_read(v_h_3036_, v_bytes_3037_);
stack->m_obj
 = v_res_3039_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_read___boxed(lean_object* v_h_3040_, lean_object* v_bytes_3041_, lean_object* v_a_00___x40___internal___hyg_3042_){
_start:
{
size_t v_bytes_boxed_3043_; lean_object* v_res_3044_; 
v_bytes_boxed_3043_ = lean_unbox_usize(v_bytes_3041_);
lean_dec(v_bytes_3041_);
v_res_3044_ = lean_io_prim_handle_read(v_h_3040_, v_bytes_boxed_3043_);
lean_dec(v_h_3040_);
return v_res_3044_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_write_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3045_ = stack[0].m_obj;
lean_object* v_buffer_3046_ = stack[1].m_obj;
lean_object* v_res_3048_;
v_res_3048_ = lean_io_prim_handle_write(v_h_3045_, v_buffer_3046_);
stack->m_obj
 = v_res_3048_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_write___boxed(lean_object* v_h_3049_, lean_object* v_buffer_3050_, lean_object* v_a_00___x40___internal___hyg_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = lean_io_prim_handle_write(v_h_3049_, v_buffer_3050_);
lean_dec_ref(v_buffer_3050_);
lean_dec(v_h_3049_);
return v_res_3052_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_getLine_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3053_ = stack[0].m_obj;
lean_object* v_res_3055_;
v_res_3055_ = lean_io_prim_handle_get_line(v_h_3053_);
stack->m_obj
 = v_res_3055_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_getLine___boxed(lean_object* v_h_3056_, lean_object* v_a_00___x40___internal___hyg_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = lean_io_prim_handle_get_line(v_h_3056_);
lean_dec(v_h_3056_);
return v_res_3058_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_putStr_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3059_ = stack[0].m_obj;
lean_object* v_s_3060_ = stack[1].m_obj;
lean_object* v_res_3062_;
v_res_3062_ = lean_io_prim_handle_put_str(v_h_3059_, v_s_3060_);
stack->m_obj
 = v_res_3062_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStr___boxed(lean_object* v_h_3063_, lean_object* v_s_3064_, lean_object* v_a_00___x40___internal___hyg_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = lean_io_prim_handle_put_str(v_h_3063_, v_s_3064_);
lean_dec_ref(v_s_3064_);
lean_dec(v_h_3063_);
return v_res_3066_;
}
}
LEAN_EXPORT void l_IO_FS_realPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_fname_3067_ = stack[0].m_obj;
lean_object* v_res_3069_;
v_res_3069_ = lean_io_realpath(v_fname_3067_);
stack->m_obj
 = v_res_3069_;
}
LEAN_EXPORT lean_object* l_IO_FS_realPath___boxed(lean_object* v_fname_3070_, lean_object* v_a_00___x40___internal___hyg_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = lean_io_realpath(v_fname_3070_);
return v_res_3072_;
}
}
LEAN_EXPORT void l_IO_FS_removeFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_fname_3073_ = stack[0].m_obj;
lean_object* v_res_3075_;
v_res_3075_ = lean_io_remove_file(v_fname_3073_);
stack->m_obj
 = v_res_3075_;
}
LEAN_EXPORT lean_object* l_IO_FS_removeFile___boxed(lean_object* v_fname_3076_, lean_object* v_a_00___x40___internal___hyg_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = lean_io_remove_file(v_fname_3076_);
lean_dec_ref(v_fname_3076_);
return v_res_3078_;
}
}
LEAN_EXPORT void l_IO_FS_removeDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_3079_ = stack[0].m_obj;
lean_object* v_res_3081_;
v_res_3081_ = lean_io_remove_dir(v_a_00___x40___internal___hyg_3079_);
stack->m_obj
 = v_res_3081_;
}
LEAN_EXPORT lean_object* l_IO_FS_removeDir___boxed(lean_object* v_a_00___x40___internal___hyg_3082_, lean_object* v_a_00___x40___internal___hyg_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = lean_io_remove_dir(v_a_00___x40___internal___hyg_3082_);
lean_dec_ref(v_a_00___x40___internal___hyg_3082_);
return v_res_3084_;
}
}
LEAN_EXPORT void l_IO_FS_createDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_3085_ = stack[0].m_obj;
lean_object* v_res_3087_;
v_res_3087_ = lean_io_create_dir(v_a_00___x40___internal___hyg_3085_);
stack->m_obj
 = v_res_3087_;
}
LEAN_EXPORT lean_object* l_IO_FS_createDir___boxed(lean_object* v_a_00___x40___internal___hyg_3088_, lean_object* v_a_00___x40___internal___hyg_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = lean_io_create_dir(v_a_00___x40___internal___hyg_3088_);
lean_dec_ref(v_a_00___x40___internal___hyg_3088_);
return v_res_3090_;
}
}
LEAN_EXPORT void l_IO_FS_rename_0interp(lean_interpreter_value* stack)
{
lean_object* v_old_3091_ = stack[0].m_obj;
lean_object* v_new_3092_ = stack[1].m_obj;
lean_object* v_res_3094_;
v_res_3094_ = lean_io_rename(v_old_3091_, v_new_3092_);
stack->m_obj
 = v_res_3094_;
}
LEAN_EXPORT lean_object* l_IO_FS_rename___boxed(lean_object* v_old_3095_, lean_object* v_new_3096_, lean_object* v_a_00___x40___internal___hyg_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = lean_io_rename(v_old_3095_, v_new_3096_);
lean_dec_ref(v_new_3096_);
lean_dec_ref(v_old_3095_);
return v_res_3098_;
}
}
LEAN_EXPORT void l_IO_FS_hardLink_0interp(lean_interpreter_value* stack)
{
lean_object* v_orig_3099_ = stack[0].m_obj;
lean_object* v_link_3100_ = stack[1].m_obj;
lean_object* v_res_3102_;
v_res_3102_ = lean_io_hard_link(v_orig_3099_, v_link_3100_);
stack->m_obj
 = v_res_3102_;
}
LEAN_EXPORT lean_object* l_IO_FS_hardLink___boxed(lean_object* v_orig_3103_, lean_object* v_link_3104_, lean_object* v_a_00___x40___internal___hyg_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = lean_io_hard_link(v_orig_3103_, v_link_3104_);
lean_dec_ref(v_link_3104_);
lean_dec_ref(v_orig_3103_);
return v_res_3106_;
}
}
LEAN_EXPORT void l_IO_FS_createTempFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3108_;
v_res_3108_ = lean_io_create_tempfile();
stack->m_obj
 = v_res_3108_;
}
LEAN_EXPORT lean_object* l_IO_FS_createTempFile___boxed(lean_object* v_a_00___x40___internal___hyg_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = lean_io_create_tempfile();
return v_res_3110_;
}
}
LEAN_EXPORT void l_IO_FS_createTempDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3112_;
v_res_3112_ = lean_io_create_tempdir();
stack->m_obj
 = v_res_3112_;
}
LEAN_EXPORT lean_object* l_IO_FS_createTempDir___boxed(lean_object* v_a_00___x40___internal___hyg_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = lean_io_create_tempdir();
return v_res_3114_;
}
}
LEAN_EXPORT void l_IO_getEnv_0interp(lean_interpreter_value* stack)
{
lean_object* v_var_3115_ = stack[0].m_obj;
lean_object* v_res_3117_;
v_res_3117_ = lean_io_getenv(v_var_3115_);
stack->m_obj
 = v_res_3117_;
}
LEAN_EXPORT lean_object* l_IO_getEnv___boxed(lean_object* v_var_3118_, lean_object* v_a_00___x40___internal___hyg_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = lean_io_getenv(v_var_3118_);
lean_dec_ref(v_var_3118_);
return v_res_3120_;
}
}
LEAN_EXPORT void l_IO_appPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3122_;
v_res_3122_ = lean_io_app_path();
stack->m_obj
 = v_res_3122_;
}
LEAN_EXPORT lean_object* l_IO_appPath___boxed(lean_object* v_a_00___x40___internal___hyg_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = lean_io_app_path();
return v_res_3124_;
}
}
LEAN_EXPORT void l_IO_currentDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3126_;
v_res_3126_ = lean_io_current_dir();
stack->m_obj
 = v_res_3126_;
}
LEAN_EXPORT lean_object* l_IO_currentDir___boxed(lean_object* v_a_00___x40___internal___hyg_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = lean_io_current_dir();
return v_res_3128_;
}
}
lean_object* l_IO_FS_withFile___redArg(lean_object* v_fn_3129_, uint8_t v_mode_3130_, lean_object* v_f_3131_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = lean_io_prim_handle_mk(v_fn_3129_, v_mode_3130_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3135_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_a_3134_);
lean_dec_ref_known(v___x_3133_, 1);
v___x_3135_ = lean_apply_2(v_f_3131_, v_a_3134_, lean_box(0));
return v___x_3135_;
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec_ref(v_f_3131_);
v_a_3136_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3133_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3133_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_withFile___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_3129_ = stack[0].m_obj;
uint8_t v_mode_3130_ = stack[1].m_num;
lean_object* v_f_3131_ = stack[2].m_obj;
lean_object* v_res_3144_;
v_res_3144_ = l_IO_FS_withFile___redArg(v_fn_3129_, v_mode_3130_, v_f_3131_);
stack->m_obj
 = v_res_3144_;
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___redArg___boxed(lean_object* v_fn_3145_, lean_object* v_mode_3146_, lean_object* v_f_3147_, lean_object* v_a_3148_){
_start:
{
uint8_t v_mode_boxed_3149_; lean_object* v_res_3150_; 
v_mode_boxed_3149_ = lean_unbox(v_mode_3146_);
v_res_3150_ = l_IO_FS_withFile___redArg(v_fn_3145_, v_mode_boxed_3149_, v_f_3147_);
lean_dec_ref(v_fn_3145_);
return v_res_3150_;
}
}
lean_object* l_IO_FS_withFile(lean_object* v_00_u03b1_3151_, lean_object* v_fn_3152_, uint8_t v_mode_3153_, lean_object* v_f_3154_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = lean_io_prim_handle_mk(v_fn_3152_, v_mode_3153_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3158_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_a_3157_);
lean_dec_ref_known(v___x_3156_, 1);
v___x_3158_ = lean_apply_2(v_f_3154_, v_a_3157_, lean_box(0));
return v___x_3158_;
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec_ref(v_f_3154_);
v_a_3159_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3156_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3156_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_withFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_3152_ = stack[1].m_obj;
uint8_t v_mode_3153_ = stack[2].m_num;
lean_object* v_f_3154_ = stack[3].m_obj;
lean_object* v_res_3167_;
v_res_3167_ = l_IO_FS_withFile(lean_box(0), v_fn_3152_, v_mode_3153_, v_f_3154_);
stack->m_obj
 = v_res_3167_;
}
LEAN_EXPORT lean_object* l_IO_FS_withFile___boxed(lean_object* v_00_u03b1_3168_, lean_object* v_fn_3169_, lean_object* v_mode_3170_, lean_object* v_f_3171_, lean_object* v_a_3172_){
_start:
{
uint8_t v_mode_boxed_3173_; lean_object* v_res_3174_; 
v_mode_boxed_3173_ = lean_unbox(v_mode_3170_);
v_res_3174_ = l_IO_FS_withFile(v_00_u03b1_3168_, v_fn_3169_, v_mode_boxed_3173_, v_f_3171_);
lean_dec_ref(v_fn_3169_);
return v_res_3174_;
}
}
lean_object* l_IO_FS_Handle_putStrLn(lean_object* v_h_3175_, lean_object* v_s_3176_){
_start:
{
uint32_t v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = 10;
v___x_3179_ = lean_string_push(v_s_3176_, v___x_3178_);
v___x_3180_ = lean_io_prim_handle_put_str(v_h_3175_, v___x_3179_);
lean_dec_ref(v___x_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_putStrLn_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3175_ = stack[0].m_obj;
lean_object* v_s_3176_ = stack[1].m_obj;
lean_object* v_res_3181_;
v_res_3181_ = l_IO_FS_Handle_putStrLn(v_h_3175_, v_s_3176_);
stack->m_obj
 = v_res_3181_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object* v_h_3182_, lean_object* v_s_3183_, lean_object* v_a_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_IO_FS_Handle_putStrLn(v_h_3182_, v_s_3183_);
lean_dec(v_h_3182_);
return v_res_3185_;
}
}
lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(lean_object* v_h_3186_, lean_object* v_acc_3187_){
_start:
{
size_t v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((size_t)1024ULL);
v___x_3190_ = lean_io_prim_handle_read(v_h_3186_, v___x_3189_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3204_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3204_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3204_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
uint8_t v___x_3195_; 
v___x_3195_ = l_ByteArray_isEmpty(v_a_3191_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
lean_del_object(v___x_3193_);
v___x_3196_ = lean_unsigned_to_nat(0u);
v___x_3197_ = lean_byte_array_size(v_acc_3187_);
v___x_3198_ = lean_byte_array_size(v_a_3191_);
v___x_3199_ = lean_byte_array_copy_slice(v_a_3191_, v___x_3196_, v_acc_3187_, v___x_3197_, v___x_3198_, v___x_3195_);
lean_dec(v_a_3191_);
v_acc_3187_ = v___x_3199_;
goto _start;
}
else
{
lean_object* v___x_3202_; 
lean_dec(v_a_3191_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v_acc_3187_);
v___x_3202_ = v___x_3193_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_acc_3187_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_dec_ref(v_acc_3187_);
return v___x_3190_;
}
}
}
LEAN_EXPORT void l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3186_ = stack[0].m_obj;
lean_object* v_acc_3187_ = stack[1].m_obj;
lean_object* v_res_3205_;
v_res_3205_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_3186_, v_acc_3187_);
stack->m_obj
 = v_res_3205_;
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop___boxed(lean_object* v_h_3206_, lean_object* v_acc_3207_, lean_object* v_a_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_3206_, v_acc_3207_);
lean_dec(v_h_3206_);
return v_res_3209_;
}
}
lean_object* l_IO_FS_Handle_readBinToEndInto(lean_object* v_h_3210_, lean_object* v_buf_3211_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_3210_, v_buf_3211_);
return v___x_3213_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_readBinToEndInto_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3210_ = stack[0].m_obj;
lean_object* v_buf_3211_ = stack[1].m_obj;
lean_object* v_res_3214_;
v_res_3214_ = l_IO_FS_Handle_readBinToEndInto(v_h_3210_, v_buf_3211_);
stack->m_obj
 = v_res_3214_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEndInto___boxed(lean_object* v_h_3215_, lean_object* v_buf_3216_, lean_object* v_a_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_IO_FS_Handle_readBinToEndInto(v_h_3215_, v_buf_3216_);
lean_dec(v_h_3215_);
return v_res_3218_;
}
}
lean_object* l_IO_FS_Handle_readBinToEnd(lean_object* v_h_3219_){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = l_ByteArray_empty;
v___x_3222_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_h_3219_, v___x_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_readBinToEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3219_ = stack[0].m_obj;
lean_object* v_res_3223_;
v_res_3223_ = l_IO_FS_Handle_readBinToEnd(v_h_3219_);
stack->m_obj
 = v_res_3223_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readBinToEnd___boxed(lean_object* v_h_3224_, lean_object* v_a_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_IO_FS_Handle_readBinToEnd(v_h_3224_);
lean_dec(v_h_3224_);
return v_res_3226_;
}
}
lean_object* l_IO_FS_Handle_readToEnd(lean_object* v_h_3230_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_IO_FS_Handle_readBinToEnd(v_h_3230_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3246_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3235_ = v___x_3232_;
v_isShared_3236_ = v_isSharedCheck_3246_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3232_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3246_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
uint8_t v___x_3237_; 
v___x_3237_ = lean_string_validate_utf8(v_a_3233_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; lean_object* v___x_3240_; 
lean_dec(v_a_3233_);
v___x_3238_ = ((lean_object*)(l_IO_FS_Handle_readToEnd___closed__1));
if (v_isShared_3236_ == 0)
{
lean_ctor_set_tag(v___x_3235_, 1);
lean_ctor_set(v___x_3235_, 0, v___x_3238_);
v___x_3240_ = v___x_3235_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
else
{
lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3242_ = lean_string_from_utf8_unchecked(v_a_3233_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___x_3242_);
v___x_3244_ = v___x_3235_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
v_a_3247_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3232_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3232_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_Handle_readToEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3230_ = stack[0].m_obj;
lean_object* v_res_3255_;
v_res_3255_ = l_IO_FS_Handle_readToEnd(v_h_3230_);
stack->m_obj
 = v_res_3255_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_readToEnd___boxed(lean_object* v_h_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_IO_FS_Handle_readToEnd(v_h_3256_);
lean_dec(v_h_3256_);
return v_res_3258_;
}
}
lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read(lean_object* v_h_3259_, lean_object* v_lines_3260_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = lean_io_prim_handle_get_line(v_h_3259_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3320_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3265_ = v___x_3262_;
v_isShared_3266_ = v_isSharedCheck_3320_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3262_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3320_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___y_3268_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; uint32_t v___y_3275_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; uint32_t v___y_3288_; lean_object* v___x_3310_; lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3310_ = lean_string_utf8_byte_size(v_a_3263_);
v___x_3311_ = lean_unsigned_to_nat(0u);
v___x_3312_ = lean_nat_dec_eq(v___x_3310_, v___x_3311_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
lean_inc(v_a_3263_);
v___x_3313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3313_, 0, v_a_3263_);
lean_ctor_set(v___x_3313_, 1, v___x_3311_);
lean_ctor_set(v___x_3313_, 2, v___x_3310_);
v___x_3314_ = l_String_Slice_Pos_prev_x3f(v___x_3313_, v___x_3310_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_dec_ref_known(v___x_3313_, 3);
goto v___jp_3308_;
}
else
{
lean_object* v_val_3315_; lean_object* v___x_3316_; 
v_val_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_val_3315_);
lean_dec_ref_known(v___x_3314_, 1);
v___x_3316_ = l_String_Slice_Pos_get_x3f(v___x_3313_, v_val_3315_);
lean_dec(v_val_3315_);
lean_dec_ref_known(v___x_3313_, 3);
if (lean_obj_tag(v___x_3316_) == 0)
{
goto v___jp_3308_;
}
else
{
lean_object* v_val_3317_; uint32_t v___x_3318_; 
v_val_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_val_3317_);
lean_dec_ref_known(v___x_3316_, 1);
v___x_3318_ = lean_unbox_uint32(v_val_3317_);
lean_dec(v_val_3317_);
v___y_3288_ = v___x_3318_;
goto v___jp_3287_;
}
}
}
else
{
lean_object* v___x_3319_; 
lean_del_object(v___x_3265_);
lean_dec(v_a_3263_);
v___x_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3319_, 0, v_lines_3260_);
return v___x_3319_;
}
v___jp_3267_:
{
lean_object* v___x_3269_; 
v___x_3269_ = lean_array_push(v_lines_3260_, v___y_3268_);
v_lines_3260_ = v___x_3269_;
goto _start;
}
v___jp_3271_:
{
uint32_t v___x_3276_; uint8_t v___x_3277_; 
v___x_3276_ = 13;
v___x_3277_ = lean_uint32_dec_eq(v___y_3275_, v___x_3276_);
if (v___x_3277_ == 0)
{
lean_dec(v___y_3273_);
lean_dec(v___y_3272_);
v___y_3268_ = v___y_3274_;
goto v___jp_3267_;
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3278_ = lean_string_utf8_byte_size(v___y_3274_);
lean_inc(v___y_3273_);
lean_inc_ref(v___y_3274_);
v___x_3279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3279_, 0, v___y_3274_);
lean_ctor_set(v___x_3279_, 1, v___y_3273_);
lean_ctor_set(v___x_3279_, 2, v___x_3278_);
v___x_3280_ = l_String_Slice_Pos_prevn(v___x_3279_, v___x_3278_, v___y_3272_);
lean_dec_ref_known(v___x_3279_, 3);
v___x_3281_ = lean_string_utf8_extract_fast(v___y_3274_, v___y_3273_, v___x_3280_);
lean_dec(v___x_3280_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3274_);
v___y_3268_ = v___x_3281_;
goto v___jp_3267_;
}
}
v___jp_3282_:
{
uint32_t v___x_3286_; 
v___x_3286_ = 65;
v___y_3272_ = v___y_3283_;
v___y_3273_ = v___y_3285_;
v___y_3274_ = v___y_3284_;
v___y_3275_ = v___x_3286_;
goto v___jp_3271_;
}
v___jp_3287_:
{
uint32_t v___x_3289_; uint8_t v___x_3290_; 
v___x_3289_ = 10;
v___x_3290_ = lean_uint32_dec_eq(v___y_3288_, v___x_3289_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3291_ = lean_array_push(v_lines_3260_, v_a_3263_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v___x_3291_);
v___x_3293_ = v___x_3265_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
else
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
lean_del_object(v___x_3265_);
v___x_3295_ = lean_unsigned_to_nat(1u);
v___x_3296_ = lean_unsigned_to_nat(0u);
v___x_3297_ = lean_string_utf8_byte_size(v_a_3263_);
lean_inc(v_a_3263_);
v___x_3298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3298_, 0, v_a_3263_);
lean_ctor_set(v___x_3298_, 1, v___x_3296_);
lean_ctor_set(v___x_3298_, 2, v___x_3297_);
v___x_3299_ = l_String_Slice_Pos_prevn(v___x_3298_, v___x_3297_, v___x_3295_);
lean_dec_ref_known(v___x_3298_, 3);
v___x_3300_ = lean_string_utf8_extract_fast(v_a_3263_, v___x_3296_, v___x_3299_);
lean_dec(v___x_3299_);
lean_dec(v_a_3263_);
v___x_3301_ = lean_string_utf8_byte_size(v___x_3300_);
lean_inc_ref(v___x_3300_);
v___x_3302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3300_);
lean_ctor_set(v___x_3302_, 1, v___x_3296_);
lean_ctor_set(v___x_3302_, 2, v___x_3301_);
v___x_3303_ = l_String_Slice_Pos_prev_x3f(v___x_3302_, v___x_3301_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_dec_ref_known(v___x_3302_, 3);
v___y_3283_ = v___x_3295_;
v___y_3284_ = v___x_3300_;
v___y_3285_ = v___x_3296_;
goto v___jp_3282_;
}
else
{
lean_object* v_val_3304_; lean_object* v___x_3305_; 
v_val_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_val_3304_);
lean_dec_ref_known(v___x_3303_, 1);
v___x_3305_ = l_String_Slice_Pos_get_x3f(v___x_3302_, v_val_3304_);
lean_dec(v_val_3304_);
lean_dec_ref_known(v___x_3302_, 3);
if (lean_obj_tag(v___x_3305_) == 0)
{
v___y_3283_ = v___x_3295_;
v___y_3284_ = v___x_3300_;
v___y_3285_ = v___x_3296_;
goto v___jp_3282_;
}
else
{
lean_object* v_val_3306_; uint32_t v___x_3307_; 
v_val_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_val_3306_);
lean_dec_ref_known(v___x_3305_, 1);
v___x_3307_ = lean_unbox_uint32(v_val_3306_);
lean_dec(v_val_3306_);
v___y_3272_ = v___x_3295_;
v___y_3273_ = v___x_3296_;
v___y_3274_ = v___x_3300_;
v___y_3275_ = v___x_3307_;
goto v___jp_3271_;
}
}
}
}
v___jp_3308_:
{
uint32_t v___x_3309_; 
v___x_3309_ = 65;
v___y_3288_ = v___x_3309_;
goto v___jp_3287_;
}
}
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_dec_ref(v_lines_3260_);
v_a_3321_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3262_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3262_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_System_IO_0__IO_FS_Handle_lines_read_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3259_ = stack[0].m_obj;
lean_object* v_lines_3260_ = stack[1].m_obj;
lean_object* v_res_3329_;
v_res_3329_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_3259_, v_lines_3260_);
stack->m_obj
 = v_res_3329_;
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read___boxed(lean_object* v_h_3330_, lean_object* v_lines_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_3330_, v_lines_3331_);
lean_dec(v_h_3330_);
return v_res_3333_;
}
}
lean_object* l_IO_FS_Handle_lines(lean_object* v_h_3336_){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_3339_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_3336_, v___x_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT void l_IO_FS_Handle_lines_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3336_ = stack[0].m_obj;
lean_object* v_res_3340_;
v_res_3340_ = l_IO_FS_Handle_lines(v_h_3336_);
stack->m_obj
 = v_res_3340_;
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines___boxed(lean_object* v_h_3341_, lean_object* v_a_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_IO_FS_Handle_lines(v_h_3341_);
lean_dec(v_h_3341_);
return v_res_3343_;
}
}
lean_object* l_IO_FS_lines(lean_object* v_fname_3344_){
_start:
{
uint8_t v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = 0;
v___x_3347_ = lean_io_prim_handle_mk(v_fname_3344_, v___x_3346_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3349_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
v___x_3349_ = l_IO_FS_Handle_lines(v_a_3348_);
lean_dec(v_a_3348_);
return v___x_3349_;
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
v_a_3350_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3347_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3347_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_lines_0interp(lean_interpreter_value* stack)
{
lean_object* v_fname_3344_ = stack[0].m_obj;
lean_object* v_res_3358_;
v_res_3358_ = l_IO_FS_lines(v_fname_3344_);
stack->m_obj
 = v_res_3358_;
}
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object* v_fname_3359_, lean_object* v_a_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_IO_FS_lines(v_fname_3359_);
lean_dec_ref(v_fname_3359_);
return v_res_3361_;
}
}
lean_object* l_IO_FS_writeBinFile(lean_object* v_fname_3362_, lean_object* v_content_3363_){
_start:
{
uint8_t v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = 1;
v___x_3366_ = lean_io_prim_handle_mk(v_fname_3362_, v___x_3365_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3368_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
lean_dec_ref_known(v___x_3366_, 1);
v___x_3368_ = lean_io_prim_handle_write(v_a_3367_, v_content_3363_);
lean_dec(v_a_3367_);
return v___x_3368_;
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
v_a_3369_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3366_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3366_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_writeBinFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_fname_3362_ = stack[0].m_obj;
lean_object* v_content_3363_ = stack[1].m_obj;
lean_object* v_res_3377_;
v_res_3377_ = l_IO_FS_writeBinFile(v_fname_3362_, v_content_3363_);
stack->m_obj
 = v_res_3377_;
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object* v_fname_3378_, lean_object* v_content_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_IO_FS_writeBinFile(v_fname_3378_, v_content_3379_);
lean_dec_ref(v_content_3379_);
lean_dec_ref(v_fname_3378_);
return v_res_3381_;
}
}
lean_object* l_IO_FS_writeFile(lean_object* v_fname_3382_, lean_object* v_content_3383_){
_start:
{
uint8_t v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = 1;
v___x_3386_ = lean_io_prim_handle_mk(v_fname_3382_, v___x_3385_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3388_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
v___x_3388_ = lean_io_prim_handle_put_str(v_a_3387_, v_content_3383_);
lean_dec(v_a_3387_);
return v___x_3388_;
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
v_a_3389_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3386_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3386_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_writeFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_fname_3382_ = stack[0].m_obj;
lean_object* v_content_3383_ = stack[1].m_obj;
lean_object* v_res_3397_;
v_res_3397_ = l_IO_FS_writeFile(v_fname_3382_, v_content_3383_);
stack->m_obj
 = v_res_3397_;
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object* v_fname_3398_, lean_object* v_content_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_IO_FS_writeFile(v_fname_3398_, v_content_3399_);
lean_dec_ref(v_content_3399_);
lean_dec_ref(v_fname_3398_);
return v_res_3401_;
}
}
lean_object* l_IO_FS_Stream_putStrLn(lean_object* v_strm_3402_, lean_object* v_s_3403_){
_start:
{
lean_object* v_putStr_3405_; uint32_t v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v_putStr_3405_ = lean_ctor_get(v_strm_3402_, 4);
lean_inc_ref(v_putStr_3405_);
lean_dec_ref(v_strm_3402_);
v___x_3406_ = 10;
v___x_3407_ = lean_string_push(v_s_3403_, v___x_3406_);
v___x_3408_ = lean_apply_2(v_putStr_3405_, v___x_3407_, lean_box(0));
return v___x_3408_;
}
}
LEAN_EXPORT void l_IO_FS_Stream_putStrLn_0interp(lean_interpreter_value* stack)
{
lean_object* v_strm_3402_ = stack[0].m_obj;
lean_object* v_s_3403_ = stack[1].m_obj;
lean_object* v_res_3409_;
v_res_3409_ = l_IO_FS_Stream_putStrLn(v_strm_3402_, v_s_3403_);
stack->m_obj
 = v_res_3409_;
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn___boxed(lean_object* v_strm_3410_, lean_object* v_s_3411_, lean_object* v_a_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_IO_FS_Stream_putStrLn(v_strm_3410_, v_s_3411_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00IO_FS_instReprDirEntry_repr_spec__0(lean_object* v_a_3414_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = lean_nat_to_int(v_a_3414_);
return v___x_3415_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = lean_unsigned_to_nat(8u);
v___x_3430_ = lean_nat_to_int(v___x_3429_);
return v___x_3430_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = lean_unsigned_to_nat(12u);
v___x_3441_ = lean_nat_to_int(v___x_3440_);
return v___x_3441_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__0));
v___x_3444_ = lean_string_length(v___x_3443_);
return v___x_3444_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__16, &l_IO_FS_instReprDirEntry_repr___redArg___closed__16_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16);
v___x_3446_ = lean_nat_to_int(v___x_3445_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___redArg(lean_object* v_x_3451_){
_start:
{
lean_object* v_root_3452_; lean_object* v_fileName_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3492_; 
v_root_3452_ = lean_ctor_get(v_x_3451_, 0);
v_fileName_3453_ = lean_ctor_get(v_x_3451_, 1);
v_isSharedCheck_3492_ = !lean_is_exclusive(v_x_3451_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3455_ = v_x_3451_;
v_isShared_3456_ = v_isSharedCheck_3492_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_fileName_3453_);
lean_inc(v_root_3452_);
lean_dec(v_x_3451_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3492_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3457_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3458_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__6));
v___x_3459_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3460_ = lean_unsigned_to_nat(0u);
v___x_3461_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__9));
v___x_3462_ = l_String_quote(v_root_3452_);
v___x_3463_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set_tag(v___x_3455_, 5);
lean_ctor_set(v___x_3455_, 1, v___x_3463_);
lean_ctor_set(v___x_3455_, 0, v___x_3461_);
v___x_3465_ = v___x_3455_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3461_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; uint8_t v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3466_ = l_Repr_addAppParen(v___x_3465_, v___x_3460_);
v___x_3467_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3459_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
v___x_3468_ = 0;
v___x_3469_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3469_, 0, v___x_3467_);
lean_ctor_set_uint8(v___x_3469_, sizeof(void*)*1, v___x_3468_);
v___x_3470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3458_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3470_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
v___x_3473_ = lean_box(1);
v___x_3474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3472_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v___x_3475_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__13));
v___x_3476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3474_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
lean_ctor_set(v___x_3477_, 1, v___x_3457_);
v___x_3478_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__14, &l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14);
v___x_3479_ = l_String_quote(v_fileName_3453_);
v___x_3480_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
v___x_3481_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3478_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*1, v___x_3468_);
v___x_3483_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3477_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3485_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3486_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
lean_ctor_set(v___x_3486_, 1, v___x_3483_);
v___x_3487_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3488_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3486_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
v___x_3489_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3484_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set_uint8(v___x_3490_, sizeof(void*)*1, v___x_3468_);
return v___x_3490_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr(lean_object* v_x_3493_, lean_object* v_prec_3494_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_IO_FS_instReprDirEntry_repr___redArg(v_x_3493_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___boxed(lean_object* v_x_3496_, lean_object* v_prec_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_IO_FS_instReprDirEntry_repr(v_x_3496_, v_prec_3497_);
lean_dec(v_prec_3497_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object* v_entry_3501_){
_start:
{
lean_object* v_root_3502_; lean_object* v_fileName_3503_; lean_object* v___x_3504_; 
v_root_3502_ = lean_ctor_get(v_entry_3501_, 0);
lean_inc_ref(v_root_3502_);
v_fileName_3503_ = lean_ctor_get(v_entry_3501_, 1);
lean_inc_ref(v_fileName_3503_);
lean_dec_ref(v_entry_3501_);
v___x_3504_ = l_System_FilePath_join(v_root_3502_, v_fileName_3503_);
return v___x_3504_;
}
}
lean_object* l_IO_FS_FileType_ctorIdx___impl(uint8_t v_x_3505_){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = lean_box(v_x_3505_);
v___x_3507_ = lean_obj_tag_nat(v___x_3506_);
lean_dec(v___x_3506_);
return v___x_3507_;
}
}
LEAN_EXPORT void l_IO_FS_FileType_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_3505_ = stack[0].m_num;
lean_object* v_res_3508_;
v_res_3508_ = l_IO_FS_FileType_ctorIdx___impl(v_x_3505_);
stack->m_obj
 = v_res_3508_;
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx___impl___boxed(lean_object* v_x_3509_){
_start:
{
uint8_t v_x_4__boxed_3510_; lean_object* v_res_3511_; 
v_x_4__boxed_3510_ = lean_unbox(v_x_3509_);
v_res_3511_ = l_IO_FS_FileType_ctorIdx___impl(v_x_4__boxed_3510_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg(lean_object* v_k_3512_){
_start:
{
lean_inc(v_k_3512_);
return v_k_3512_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg___boxed(lean_object* v_k_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_IO_FS_FileType_ctorElim___redArg(v_k_3513_);
lean_dec(v_k_3513_);
return v_res_3514_;
}
}
lean_object* l_IO_FS_FileType_ctorElim(lean_object* v_motive_3515_, lean_object* v_ctorIdx_3516_, uint8_t v_t_3517_, lean_object* v_h_3518_, lean_object* v_k_3519_){
_start:
{
lean_inc(v_k_3519_);
return v_k_3519_;
}
}
LEAN_EXPORT void l_IO_FS_FileType_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_3516_ = stack[1].m_obj;
uint8_t v_t_3517_ = stack[2].m_num;
lean_object* v_k_3519_ = stack[4].m_obj;
lean_object* v_res_3520_;
v_res_3520_ = l_IO_FS_FileType_ctorElim(lean_box(0), v_ctorIdx_3516_, v_t_3517_, lean_box(0), v_k_3519_);
stack->m_obj
 = v_res_3520_;
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___boxed(lean_object* v_motive_3521_, lean_object* v_ctorIdx_3522_, lean_object* v_t_3523_, lean_object* v_h_3524_, lean_object* v_k_3525_){
_start:
{
uint8_t v_t_boxed_3526_; lean_object* v_res_3527_; 
v_t_boxed_3526_ = lean_unbox(v_t_3523_);
v_res_3527_ = l_IO_FS_FileType_ctorElim(v_motive_3521_, v_ctorIdx_3522_, v_t_boxed_3526_, v_h_3524_, v_k_3525_);
lean_dec(v_k_3525_);
lean_dec(v_ctorIdx_3522_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg(lean_object* v_dir_3528_){
_start:
{
lean_inc(v_dir_3528_);
return v_dir_3528_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg___boxed(lean_object* v_dir_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_IO_FS_FileType_dir_elim___redArg(v_dir_3529_);
lean_dec(v_dir_3529_);
return v_res_3530_;
}
}
lean_object* l_IO_FS_FileType_dir_elim(lean_object* v_motive_3531_, uint8_t v_t_3532_, lean_object* v_h_3533_, lean_object* v_dir_3534_){
_start:
{
lean_inc(v_dir_3534_);
return v_dir_3534_;
}
}
LEAN_EXPORT void l_IO_FS_FileType_dir_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_3532_ = stack[1].m_num;
lean_object* v_dir_3534_ = stack[3].m_obj;
lean_object* v_res_3535_;
v_res_3535_ = l_IO_FS_FileType_dir_elim(lean_box(0), v_t_3532_, lean_box(0), v_dir_3534_);
stack->m_obj
 = v_res_3535_;
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___boxed(lean_object* v_motive_3536_, lean_object* v_t_3537_, lean_object* v_h_3538_, lean_object* v_dir_3539_){
_start:
{
uint8_t v_t_boxed_3540_; lean_object* v_res_3541_; 
v_t_boxed_3540_ = lean_unbox(v_t_3537_);
v_res_3541_ = l_IO_FS_FileType_dir_elim(v_motive_3536_, v_t_boxed_3540_, v_h_3538_, v_dir_3539_);
lean_dec(v_dir_3539_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg(lean_object* v_file_3542_){
_start:
{
lean_inc(v_file_3542_);
return v_file_3542_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg___boxed(lean_object* v_file_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_IO_FS_FileType_file_elim___redArg(v_file_3543_);
lean_dec(v_file_3543_);
return v_res_3544_;
}
}
lean_object* l_IO_FS_FileType_file_elim(lean_object* v_motive_3545_, uint8_t v_t_3546_, lean_object* v_h_3547_, lean_object* v_file_3548_){
_start:
{
lean_inc(v_file_3548_);
return v_file_3548_;
}
}
LEAN_EXPORT void l_IO_FS_FileType_file_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_3546_ = stack[1].m_num;
lean_object* v_file_3548_ = stack[3].m_obj;
lean_object* v_res_3549_;
v_res_3549_ = l_IO_FS_FileType_file_elim(lean_box(0), v_t_3546_, lean_box(0), v_file_3548_);
stack->m_obj
 = v_res_3549_;
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___boxed(lean_object* v_motive_3550_, lean_object* v_t_3551_, lean_object* v_h_3552_, lean_object* v_file_3553_){
_start:
{
uint8_t v_t_boxed_3554_; lean_object* v_res_3555_; 
v_t_boxed_3554_ = lean_unbox(v_t_3551_);
v_res_3555_ = l_IO_FS_FileType_file_elim(v_motive_3550_, v_t_boxed_3554_, v_h_3552_, v_file_3553_);
lean_dec(v_file_3553_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg(lean_object* v_symlink_3556_){
_start:
{
lean_inc(v_symlink_3556_);
return v_symlink_3556_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg___boxed(lean_object* v_symlink_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_IO_FS_FileType_symlink_elim___redArg(v_symlink_3557_);
lean_dec(v_symlink_3557_);
return v_res_3558_;
}
}
lean_object* l_IO_FS_FileType_symlink_elim(lean_object* v_motive_3559_, uint8_t v_t_3560_, lean_object* v_h_3561_, lean_object* v_symlink_3562_){
_start:
{
lean_inc(v_symlink_3562_);
return v_symlink_3562_;
}
}
LEAN_EXPORT void l_IO_FS_FileType_symlink_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_3560_ = stack[1].m_num;
lean_object* v_symlink_3562_ = stack[3].m_obj;
lean_object* v_res_3563_;
v_res_3563_ = l_IO_FS_FileType_symlink_elim(lean_box(0), v_t_3560_, lean_box(0), v_symlink_3562_);
stack->m_obj
 = v_res_3563_;
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___boxed(lean_object* v_motive_3564_, lean_object* v_t_3565_, lean_object* v_h_3566_, lean_object* v_symlink_3567_){
_start:
{
uint8_t v_t_boxed_3568_; lean_object* v_res_3569_; 
v_t_boxed_3568_ = lean_unbox(v_t_3565_);
v_res_3569_ = l_IO_FS_FileType_symlink_elim(v_motive_3564_, v_t_boxed_3568_, v_h_3566_, v_symlink_3567_);
lean_dec(v_symlink_3567_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg(lean_object* v_other_3570_){
_start:
{
lean_inc(v_other_3570_);
return v_other_3570_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg___boxed(lean_object* v_other_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_IO_FS_FileType_other_elim___redArg(v_other_3571_);
lean_dec(v_other_3571_);
return v_res_3572_;
}
}
lean_object* l_IO_FS_FileType_other_elim(lean_object* v_motive_3573_, uint8_t v_t_3574_, lean_object* v_h_3575_, lean_object* v_other_3576_){
_start:
{
lean_inc(v_other_3576_);
return v_other_3576_;
}
}
LEAN_EXPORT void l_IO_FS_FileType_other_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_3574_ = stack[1].m_num;
lean_object* v_other_3576_ = stack[3].m_obj;
lean_object* v_res_3577_;
v_res_3577_ = l_IO_FS_FileType_other_elim(lean_box(0), v_t_3574_, lean_box(0), v_other_3576_);
stack->m_obj
 = v_res_3577_;
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___boxed(lean_object* v_motive_3578_, lean_object* v_t_3579_, lean_object* v_h_3580_, lean_object* v_other_3581_){
_start:
{
uint8_t v_t_boxed_3582_; lean_object* v_res_3583_; 
v_t_boxed_3582_ = lean_unbox(v_t_3579_);
v_res_3583_ = l_IO_FS_FileType_other_elim(v_motive_3578_, v_t_boxed_3582_, v_h_3580_, v_other_3581_);
lean_dec(v_other_3581_);
return v_res_3583_;
}
}
lean_object* l_IO_FS_instReprFileType_repr(uint8_t v_x_3596_, lean_object* v_prec_3597_){
_start:
{
lean_object* v___y_3599_; lean_object* v___y_3606_; lean_object* v___y_3613_; lean_object* v___y_3620_; 
switch(v_x_3596_)
{
case 0:
{
lean_object* v___x_3626_; uint8_t v___x_3627_; 
v___x_3626_ = lean_unsigned_to_nat(1024u);
v___x_3627_ = lean_nat_dec_le(v___x_3626_, v_prec_3597_);
if (v___x_3627_ == 0)
{
lean_object* v___x_3628_; 
v___x_3628_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3599_ = v___x_3628_;
goto v___jp_3598_;
}
else
{
lean_object* v___x_3629_; 
v___x_3629_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3599_ = v___x_3629_;
goto v___jp_3598_;
}
}
case 1:
{
lean_object* v___x_3630_; uint8_t v___x_3631_; 
v___x_3630_ = lean_unsigned_to_nat(1024u);
v___x_3631_ = lean_nat_dec_le(v___x_3630_, v_prec_3597_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; 
v___x_3632_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3606_ = v___x_3632_;
goto v___jp_3605_;
}
else
{
lean_object* v___x_3633_; 
v___x_3633_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3606_ = v___x_3633_;
goto v___jp_3605_;
}
}
case 2:
{
lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3634_ = lean_unsigned_to_nat(1024u);
v___x_3635_ = lean_nat_dec_le(v___x_3634_, v_prec_3597_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; 
v___x_3636_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3613_ = v___x_3636_;
goto v___jp_3612_;
}
else
{
lean_object* v___x_3637_; 
v___x_3637_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3613_ = v___x_3637_;
goto v___jp_3612_;
}
}
default: 
{
lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3638_ = lean_unsigned_to_nat(1024u);
v___x_3639_ = lean_nat_dec_le(v___x_3638_, v_prec_3597_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; 
v___x_3640_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3620_ = v___x_3640_;
goto v___jp_3619_;
}
else
{
lean_object* v___x_3641_; 
v___x_3641_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3620_ = v___x_3641_;
goto v___jp_3619_;
}
}
}
v___jp_3598_:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; uint8_t v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3600_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__1));
lean_inc(v___y_3599_);
v___x_3601_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___y_3599_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v___x_3602_ = 0;
v___x_3603_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3603_, 0, v___x_3601_);
lean_ctor_set_uint8(v___x_3603_, sizeof(void*)*1, v___x_3602_);
v___x_3604_ = l_Repr_addAppParen(v___x_3603_, v_prec_3597_);
return v___x_3604_;
}
v___jp_3605_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3607_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__3));
lean_inc(v___y_3606_);
v___x_3608_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___y_3606_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = 0;
v___x_3610_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3610_, 0, v___x_3608_);
lean_ctor_set_uint8(v___x_3610_, sizeof(void*)*1, v___x_3609_);
v___x_3611_ = l_Repr_addAppParen(v___x_3610_, v_prec_3597_);
return v___x_3611_;
}
v___jp_3612_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; uint8_t v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3614_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__5));
lean_inc(v___y_3613_);
v___x_3615_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___y_3613_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = 0;
v___x_3617_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3617_, 0, v___x_3615_);
lean_ctor_set_uint8(v___x_3617_, sizeof(void*)*1, v___x_3616_);
v___x_3618_ = l_Repr_addAppParen(v___x_3617_, v_prec_3597_);
return v___x_3618_;
}
v___jp_3619_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; uint8_t v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3621_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__7));
lean_inc(v___y_3620_);
v___x_3622_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___y_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = 0;
v___x_3624_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3624_, 0, v___x_3622_);
lean_ctor_set_uint8(v___x_3624_, sizeof(void*)*1, v___x_3623_);
v___x_3625_ = l_Repr_addAppParen(v___x_3624_, v_prec_3597_);
return v___x_3625_;
}
}
}
LEAN_EXPORT void l_IO_FS_instReprFileType_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_3596_ = stack[0].m_num;
lean_object* v_prec_3597_ = stack[1].m_obj;
lean_object* v_res_3642_;
v_res_3642_ = l_IO_FS_instReprFileType_repr(v_x_3596_, v_prec_3597_);
stack->m_obj
 = v_res_3642_;
}
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr___boxed(lean_object* v_x_3643_, lean_object* v_prec_3644_){
_start:
{
uint8_t v_x_221__boxed_3645_; lean_object* v_res_3646_; 
v_x_221__boxed_3645_ = lean_unbox(v_x_3643_);
v_res_3646_ = l_IO_FS_instReprFileType_repr(v_x_221__boxed_3645_, v_prec_3644_);
lean_dec(v_prec_3644_);
return v_res_3646_;
}
}
uint8_t l_IO_FS_instBEqFileType_beq(uint8_t v_x_3649_, uint8_t v_y_3650_){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; 
v___x_3651_ = lean_box(v_x_3649_);
v___x_3652_ = lean_obj_tag_nat(v___x_3651_);
lean_dec(v___x_3651_);
v___x_3653_ = lean_box(v_y_3650_);
v___x_3654_ = lean_obj_tag_nat(v___x_3653_);
lean_dec(v___x_3653_);
v___x_3655_ = lean_nat_dec_eq(v___x_3652_, v___x_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT void l_IO_FS_instBEqFileType_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_3649_ = stack[0].m_num;
uint8_t v_y_3650_ = stack[1].m_num;
uint8_t v_res_3656_;
v_res_3656_ = l_IO_FS_instBEqFileType_beq(v_x_3649_, v_y_3650_);
stack->m_num = v_res_3656_;
}
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType_beq___boxed(lean_object* v_x_3657_, lean_object* v_y_3658_){
_start:
{
uint8_t v_x_24__boxed_3659_; uint8_t v_y_25__boxed_3660_; uint8_t v_res_3661_; lean_object* v_r_3662_; 
v_x_24__boxed_3659_ = lean_unbox(v_x_3657_);
v_y_25__boxed_3660_ = lean_unbox(v_y_3658_);
v_res_3661_ = l_IO_FS_instBEqFileType_beq(v_x_24__boxed_3659_, v_y_25__boxed_3660_);
v_r_3662_ = lean_box(v_res_3661_);
return v_r_3662_;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = lean_unsigned_to_nat(7u);
v___x_3675_ = lean_nat_to_int(v___x_3674_);
return v___x_3675_;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = lean_unsigned_to_nat(0u);
v___x_3680_ = lean_nat_to_int(v___x_3679_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object* v_x_3681_){
_start:
{
lean_object* v_sec_3682_; uint32_t v_nsec_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___y_3688_; lean_object* v___x_3714_; lean_object* v___x_3715_; uint8_t v___x_3716_; 
v_sec_3682_ = lean_ctor_get(v_x_3681_, 0);
v_nsec_3683_ = lean_ctor_get_uint32(v_x_3681_, sizeof(void*)*1);
v___x_3684_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3685_ = ((lean_object*)(l_IO_FS_instReprSystemTime_repr___redArg___closed__3));
v___x_3686_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__4, &l_IO_FS_instReprSystemTime_repr___redArg___closed__4_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4);
v___x_3714_ = lean_unsigned_to_nat(0u);
v___x_3715_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__7, &l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7);
v___x_3716_ = lean_int_dec_lt(v_sec_3682_, v___x_3715_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = l_Int_repr(v_sec_3682_);
v___x_3718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
v___y_3688_ = v___x_3718_;
goto v___jp_3687_;
}
else
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3719_ = l_Int_repr(v_sec_3682_);
v___x_3720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
v___x_3721_ = l_Repr_addAppParen(v___x_3720_, v___x_3714_);
v___y_3688_ = v___x_3721_;
goto v___jp_3687_;
}
v___jp_3687_:
{
lean_object* v___x_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3689_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3686_);
lean_ctor_set(v___x_3689_, 1, v___y_3688_);
v___x_3690_ = 0;
v___x_3691_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3691_, 0, v___x_3689_);
lean_ctor_set_uint8(v___x_3691_, sizeof(void*)*1, v___x_3690_);
v___x_3692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3685_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v___x_3695_ = lean_box(1);
v___x_3696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = ((lean_object*)(l_IO_FS_instReprSystemTime_repr___redArg___closed__6));
v___x_3698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3696_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
lean_ctor_set(v___x_3699_, 1, v___x_3684_);
v___x_3700_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3701_ = lean_uint32_to_nat(v_nsec_3683_);
v___x_3702_ = l_Nat_reprFast(v___x_3701_);
v___x_3703_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
v___x_3704_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3700_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
lean_ctor_set_uint8(v___x_3705_, sizeof(void*)*1, v___x_3690_);
v___x_3706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3699_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3708_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3708_);
lean_ctor_set(v___x_3709_, 1, v___x_3706_);
v___x_3710_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___x_3712_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3707_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
lean_ctor_set_uint8(v___x_3713_, sizeof(void*)*1, v___x_3690_);
return v___x_3713_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg___boxed(lean_object* v_x_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_3722_);
lean_dec_ref(v_x_3722_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr(lean_object* v_x_3724_, lean_object* v_prec_3725_){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_3724_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___boxed(lean_object* v_x_3727_, lean_object* v_prec_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_IO_FS_instReprSystemTime_repr(v_x_3727_, v_prec_3728_);
lean_dec(v_prec_3728_);
lean_dec_ref(v_x_3727_);
return v_res_3729_;
}
}
uint8_t l_IO_FS_instBEqSystemTime_beq(lean_object* v_x_3732_, lean_object* v_x_3733_){
_start:
{
lean_object* v_sec_3734_; uint32_t v_nsec_3735_; lean_object* v_sec_3736_; uint32_t v_nsec_3737_; uint8_t v___x_3738_; 
v_sec_3734_ = lean_ctor_get(v_x_3732_, 0);
v_nsec_3735_ = lean_ctor_get_uint32(v_x_3732_, sizeof(void*)*1);
v_sec_3736_ = lean_ctor_get(v_x_3733_, 0);
v_nsec_3737_ = lean_ctor_get_uint32(v_x_3733_, sizeof(void*)*1);
v___x_3738_ = lean_int_dec_eq(v_sec_3734_, v_sec_3736_);
if (v___x_3738_ == 0)
{
return v___x_3738_;
}
else
{
uint8_t v___x_3739_; 
v___x_3739_ = lean_uint32_dec_eq(v_nsec_3735_, v_nsec_3737_);
return v___x_3739_;
}
}
}
LEAN_EXPORT void l_IO_FS_instBEqSystemTime_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3732_ = stack[0].m_obj;
lean_object* v_x_3733_ = stack[1].m_obj;
uint8_t v_res_3740_;
v_res_3740_ = l_IO_FS_instBEqSystemTime_beq(v_x_3732_, v_x_3733_);
stack->m_num = v_res_3740_;
}
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime_beq___boxed(lean_object* v_x_3741_, lean_object* v_x_3742_){
_start:
{
uint8_t v_res_3743_; lean_object* v_r_3744_; 
v_res_3743_ = l_IO_FS_instBEqSystemTime_beq(v_x_3741_, v_x_3742_);
lean_dec_ref(v_x_3742_);
lean_dec_ref(v_x_3741_);
v_r_3744_ = lean_box(v_res_3743_);
return v_r_3744_;
}
}
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object* v_x_3747_, lean_object* v_x_3748_){
_start:
{
lean_object* v_sec_3749_; uint32_t v_nsec_3750_; lean_object* v_sec_3751_; uint32_t v_nsec_3752_; uint8_t v___x_3753_; 
v_sec_3749_ = lean_ctor_get(v_x_3747_, 0);
v_nsec_3750_ = lean_ctor_get_uint32(v_x_3747_, sizeof(void*)*1);
v_sec_3751_ = lean_ctor_get(v_x_3748_, 0);
v_nsec_3752_ = lean_ctor_get_uint32(v_x_3748_, sizeof(void*)*1);
v___x_3753_ = lean_int_dec_lt(v_sec_3749_, v_sec_3751_);
if (v___x_3753_ == 0)
{
uint8_t v___x_3754_; 
v___x_3754_ = lean_int_dec_eq(v_sec_3749_, v_sec_3751_);
if (v___x_3754_ == 0)
{
uint8_t v___x_3755_; 
v___x_3755_ = 2;
return v___x_3755_;
}
else
{
uint8_t v___x_3756_; 
v___x_3756_ = lean_uint32_dec_lt(v_nsec_3750_, v_nsec_3752_);
if (v___x_3756_ == 0)
{
uint8_t v___x_3757_; 
v___x_3757_ = lean_uint32_dec_eq(v_nsec_3750_, v_nsec_3752_);
if (v___x_3757_ == 0)
{
uint8_t v___x_3758_; 
v___x_3758_ = 2;
return v___x_3758_;
}
else
{
uint8_t v___x_3759_; 
v___x_3759_ = 1;
return v___x_3759_;
}
}
else
{
uint8_t v___x_3760_; 
v___x_3760_ = 0;
return v___x_3760_;
}
}
}
else
{
uint8_t v___x_3761_; 
v___x_3761_ = 0;
return v___x_3761_;
}
}
}
LEAN_EXPORT void l_IO_FS_instOrdSystemTime_ord_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3747_ = stack[0].m_obj;
lean_object* v_x_3748_ = stack[1].m_obj;
uint8_t v_res_3762_;
v_res_3762_ = l_IO_FS_instOrdSystemTime_ord(v_x_3747_, v_x_3748_);
stack->m_num = v_res_3762_;
}
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime_ord___boxed(lean_object* v_x_3763_, lean_object* v_x_3764_){
_start:
{
uint8_t v_res_3765_; lean_object* v_r_3766_; 
v_res_3765_ = l_IO_FS_instOrdSystemTime_ord(v_x_3763_, v_x_3764_);
lean_dec_ref(v_x_3764_);
lean_dec_ref(v_x_3763_);
v_r_3766_ = lean_box(v_res_3765_);
return v_r_3766_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default___closed__0(void){
_start:
{
uint32_t v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3769_ = 0;
v___x_3770_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__7, &l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7);
v___x_3771_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
lean_ctor_set_uint32(v___x_3771_, sizeof(void*)*1, v___x_3769_);
return v___x_3771_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default(void){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = lean_obj_once(&l_IO_FS_instInhabitedSystemTime_default___closed__0, &l_IO_FS_instInhabitedSystemTime_default___closed__0_once, _init_l_IO_FS_instInhabitedSystemTime_default___closed__0);
return v___x_3772_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime(void){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_IO_FS_instInhabitedSystemTime_default;
return v___x_3773_;
}
}
static lean_object* _init_l_IO_FS_instLTSystemTime(void){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = lean_box(0);
return v___x_3774_;
}
}
static lean_object* _init_l_IO_FS_instLESystemTime(void){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = lean_box(0);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg(lean_object* v_x_3797_){
_start:
{
lean_object* v_accessed_3798_; lean_object* v_modified_3799_; uint64_t v_byteSize_3800_; uint8_t v_type_3801_; uint64_t v_numLinks_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v_accessed_3798_ = lean_ctor_get(v_x_3797_, 0);
v_modified_3799_ = lean_ctor_get(v_x_3797_, 1);
v_byteSize_3800_ = lean_ctor_get_uint64(v_x_3797_, sizeof(void*)*2);
v_type_3801_ = lean_ctor_get_uint8(v_x_3797_, sizeof(void*)*2 + 16);
v_numLinks_3802_ = lean_ctor_get_uint64(v_x_3797_, sizeof(void*)*2 + 8);
v___x_3803_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3804_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__3));
v___x_3805_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__14, &l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14);
v___x_3806_ = lean_unsigned_to_nat(0u);
v___x_3807_ = l_IO_FS_instReprSystemTime_repr___redArg(v_accessed_3798_);
v___x_3808_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3805_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = 0;
v___x_3810_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3810_, 0, v___x_3808_);
lean_ctor_set_uint8(v___x_3810_, sizeof(void*)*1, v___x_3809_);
v___x_3811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3804_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3811_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = lean_box(1);
v___x_3815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3813_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__5));
v___x_3817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3815_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3817_);
lean_ctor_set(v___x_3818_, 1, v___x_3803_);
v___x_3819_ = l_IO_FS_instReprSystemTime_repr___redArg(v_modified_3799_);
v___x_3820_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3805_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*1, v___x_3809_);
v___x_3822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3818_);
lean_ctor_set(v___x_3822_, 1, v___x_3821_);
v___x_3823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
lean_ctor_set(v___x_3823_, 1, v___x_3812_);
v___x_3824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
lean_ctor_set(v___x_3824_, 1, v___x_3814_);
v___x_3825_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__7));
v___x_3826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3824_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
lean_ctor_set(v___x_3827_, 1, v___x_3803_);
v___x_3828_ = lean_uint64_to_nat(v_byteSize_3800_);
v___x_3829_ = l_Nat_reprFast(v___x_3828_);
v___x_3830_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
v___x_3831_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3805_);
lean_ctor_set(v___x_3831_, 1, v___x_3830_);
v___x_3832_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
lean_ctor_set_uint8(v___x_3832_, sizeof(void*)*1, v___x_3809_);
v___x_3833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3827_);
lean_ctor_set(v___x_3833_, 1, v___x_3832_);
v___x_3834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
lean_ctor_set(v___x_3834_, 1, v___x_3812_);
v___x_3835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3834_);
lean_ctor_set(v___x_3835_, 1, v___x_3814_);
v___x_3836_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__9));
v___x_3837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3835_);
lean_ctor_set(v___x_3837_, 1, v___x_3836_);
v___x_3838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
lean_ctor_set(v___x_3838_, 1, v___x_3803_);
v___x_3839_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3840_ = l_IO_FS_instReprFileType_repr(v_type_3801_, v___x_3806_);
v___x_3841_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3839_);
lean_ctor_set(v___x_3841_, 1, v___x_3840_);
v___x_3842_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3842_, 0, v___x_3841_);
lean_ctor_set_uint8(v___x_3842_, sizeof(void*)*1, v___x_3809_);
v___x_3843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3838_);
lean_ctor_set(v___x_3843_, 1, v___x_3842_);
v___x_3844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3843_);
lean_ctor_set(v___x_3844_, 1, v___x_3812_);
v___x_3845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
lean_ctor_set(v___x_3845_, 1, v___x_3814_);
v___x_3846_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__11));
v___x_3847_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3845_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
lean_ctor_set(v___x_3848_, 1, v___x_3803_);
v___x_3849_ = lean_uint64_to_nat(v_numLinks_3802_);
v___x_3850_ = l_Nat_reprFast(v___x_3849_);
v___x_3851_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
v___x_3852_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3805_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
v___x_3853_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
lean_ctor_set_uint8(v___x_3853_, sizeof(void*)*1, v___x_3809_);
v___x_3854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3848_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
v___x_3855_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3856_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
lean_ctor_set(v___x_3857_, 1, v___x_3854_);
v___x_3858_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3857_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
v___x_3860_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3855_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
v___x_3861_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
lean_ctor_set_uint8(v___x_3861_, sizeof(void*)*1, v___x_3809_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg___boxed(lean_object* v_x_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_3862_);
lean_dec_ref(v_x_3862_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr(lean_object* v_x_3864_, lean_object* v_prec_3865_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_3864_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___boxed(lean_object* v_x_3867_, lean_object* v_prec_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_IO_FS_instReprMetadata_repr(v_x_3867_, v_prec_3868_);
lean_dec(v_prec_3868_);
lean_dec_ref(v_x_3867_);
return v_res_3869_;
}
}
LEAN_EXPORT void l_System_FilePath_readDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_3872_ = stack[0].m_obj;
lean_object* v_res_3874_;
v_res_3874_ = lean_io_read_dir(v_a_00___x40___internal___hyg_3872_);
stack->m_obj
 = v_res_3874_;
}
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object* v_a_00___x40___internal___hyg_3875_, lean_object* v_a_00___x40___internal___hyg_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = lean_io_read_dir(v_a_00___x40___internal___hyg_3875_);
lean_dec_ref(v_a_00___x40___internal___hyg_3875_);
return v_res_3877_;
}
}
LEAN_EXPORT void l_System_FilePath_metadata_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_3878_ = stack[0].m_obj;
lean_object* v_res_3880_;
v_res_3880_ = lean_io_metadata(v_a_00___x40___internal___hyg_3878_);
stack->m_obj
 = v_res_3880_;
}
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object* v_a_00___x40___internal___hyg_3881_, lean_object* v_a_00___x40___internal___hyg_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = lean_io_metadata(v_a_00___x40___internal___hyg_3881_);
lean_dec_ref(v_a_00___x40___internal___hyg_3881_);
return v_res_3883_;
}
}
LEAN_EXPORT void l_System_FilePath_symlinkMetadata_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_3884_ = stack[0].m_obj;
lean_object* v_res_3886_;
v_res_3886_ = lean_io_symlink_metadata(v_a_00___x40___internal___hyg_3884_);
stack->m_obj
 = v_res_3886_;
}
LEAN_EXPORT lean_object* l_System_FilePath_symlinkMetadata___boxed(lean_object* v_a_00___x40___internal___hyg_3887_, lean_object* v_a_00___x40___internal___hyg_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = lean_io_symlink_metadata(v_a_00___x40___internal___hyg_3887_);
lean_dec_ref(v_a_00___x40___internal___hyg_3887_);
return v_res_3889_;
}
}
uint8_t l_System_FilePath_isDir(lean_object* v_p_3890_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = lean_io_metadata(v_p_3890_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; uint8_t v_type_3894_; uint8_t v___x_3895_; uint8_t v___x_3896_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3892_, 1);
v_type_3894_ = lean_ctor_get_uint8(v_a_3893_, sizeof(void*)*2 + 16);
lean_dec(v_a_3893_);
v___x_3895_ = 0;
v___x_3896_ = l_IO_FS_instBEqFileType_beq(v_type_3894_, v___x_3895_);
return v___x_3896_;
}
else
{
uint8_t v___x_3897_; 
lean_dec_ref_known(v___x_3892_, 1);
v___x_3897_ = 0;
return v___x_3897_;
}
}
}
LEAN_EXPORT void l_System_FilePath_isDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3890_ = stack[0].m_obj;
uint8_t v_res_3898_;
v_res_3898_ = l_System_FilePath_isDir(v_p_3890_);
stack->m_num = v_res_3898_;
}
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object* v_p_3899_, lean_object* v_a_3900_){
_start:
{
uint8_t v_res_3901_; lean_object* v_r_3902_; 
v_res_3901_ = l_System_FilePath_isDir(v_p_3899_);
lean_dec_ref(v_p_3899_);
v_r_3902_ = lean_box(v_res_3901_);
return v_r_3902_;
}
}
uint8_t l_System_FilePath_pathExists(lean_object* v_p_3903_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = lean_io_metadata(v_p_3903_);
if (lean_obj_tag(v___x_3905_) == 0)
{
uint8_t v___x_3906_; 
lean_dec_ref_known(v___x_3905_, 1);
v___x_3906_ = 1;
return v___x_3906_;
}
else
{
uint8_t v___x_3907_; 
lean_dec_ref_known(v___x_3905_, 1);
v___x_3907_ = 0;
return v___x_3907_;
}
}
}
LEAN_EXPORT void l_System_FilePath_pathExists_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3903_ = stack[0].m_obj;
uint8_t v_res_3908_;
v_res_3908_ = l_System_FilePath_pathExists(v_p_3903_);
stack->m_num = v_res_3908_;
}
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object* v_p_3909_, lean_object* v_a_3910_){
_start:
{
uint8_t v_res_3911_; lean_object* v_r_3912_; 
v_res_3911_ = l_System_FilePath_pathExists(v_p_3909_);
lean_dec_ref(v_p_3909_);
v_r_3912_ = lean_box(v_res_3911_);
return v_r_3912_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(lean_object* v_enter_3913_, lean_object* v_p_3914_, lean_object* v_as_3915_, size_t v_sz_3916_, size_t v_i_3917_, lean_object* v_b_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v_a_3922_; lean_object* v_snd_3923_; uint8_t v___x_3927_; 
v___x_3927_ = lean_usize_dec_lt(v_i_3917_, v_sz_3916_);
if (v___x_3927_ == 0)
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
lean_dec_ref(v_p_3914_);
lean_dec_ref(v_enter_3913_);
v___x_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3928_, 0, v_b_3918_);
lean_ctor_set(v___x_3928_, 1, v___y_3919_);
v___x_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
return v___x_3929_;
}
else
{
lean_object* v___x_3930_; lean_object* v_a_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3930_ = lean_box(0);
v_a_3931_ = lean_array_uget_borrowed(v_as_3915_, v_i_3917_);
lean_inc(v_a_3931_);
v___x_3932_ = l_IO_FS_DirEntry_path(v_a_3931_);
lean_inc_ref(v___x_3932_);
v___x_3933_ = lean_array_push(v___y_3919_, v___x_3932_);
v___x_3934_ = lean_io_metadata(v___x_3932_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; uint8_t v_type_3936_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc(v_a_3935_);
lean_dec_ref_known(v___x_3934_, 1);
v_type_3936_ = lean_ctor_get_uint8(v_a_3935_, sizeof(void*)*2 + 16);
lean_dec(v_a_3935_);
switch(v_type_3936_)
{
case 2:
{
lean_object* v___x_3937_; 
v___x_3937_ = lean_io_realpath(v___x_3932_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; uint8_t v___x_3939_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref_known(v___x_3937_, 1);
v___x_3939_ = l_System_FilePath_isDir(v_a_3938_);
if (v___x_3939_ == 0)
{
lean_dec(v_a_3938_);
v_a_3922_ = v___x_3930_;
v_snd_3923_ = v___x_3933_;
goto v___jp_3921_;
}
else
{
lean_object* v___x_3940_; 
lean_inc_ref(v_enter_3913_);
lean_inc_ref(v_p_3914_);
v___x_3940_ = lean_apply_2(v_enter_3913_, v_p_3914_, lean_box(0));
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; uint8_t v___x_3942_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_a_3941_);
lean_dec_ref_known(v___x_3940_, 1);
v___x_3942_ = lean_unbox(v_a_3941_);
lean_dec(v_a_3941_);
if (v___x_3942_ == 0)
{
lean_dec(v_a_3938_);
v_a_3922_ = v___x_3930_;
v_snd_3923_ = v___x_3933_;
goto v___jp_3921_;
}
else
{
lean_object* v___x_3943_; 
lean_inc_ref(v_enter_3913_);
v___x_3943_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3913_, v_a_3938_, v___x_3933_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v_snd_3945_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v_snd_3945_ = lean_ctor_get(v_a_3944_, 1);
lean_inc(v_snd_3945_);
lean_dec(v_a_3944_);
v_a_3922_ = v___x_3930_;
v_snd_3923_ = v_snd_3945_;
goto v___jp_3921_;
}
else
{
lean_dec_ref(v_p_3914_);
lean_dec_ref(v_enter_3913_);
return v___x_3943_;
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec(v_a_3938_);
lean_dec_ref(v___x_3933_);
lean_dec_ref(v_p_3914_);
lean_dec_ref(v_enter_3913_);
v_a_3946_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3940_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3940_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec_ref(v___x_3933_);
lean_dec_ref(v_p_3914_);
lean_dec_ref(v_enter_3913_);
v_a_3954_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3937_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3937_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
case 0:
{
lean_object* v___x_3962_; 
lean_inc_ref(v_enter_3913_);
v___x_3962_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3913_, v___x_3932_, v___x_3933_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v_snd_3964_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3962_, 1);
v_snd_3964_ = lean_ctor_get(v_a_3963_, 1);
lean_inc(v_snd_3964_);
lean_dec(v_a_3963_);
v_a_3922_ = v___x_3930_;
v_snd_3923_ = v_snd_3964_;
goto v___jp_3921_;
}
else
{
lean_dec_ref(v_p_3914_);
lean_dec_ref(v_enter_3913_);
return v___x_3962_;
}
}
default: 
{
lean_dec_ref(v___x_3932_);
v_a_3922_ = v___x_3930_;
v_snd_3923_ = v___x_3933_;
goto v___jp_3921_;
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec_ref(v___x_3932_);
v_a_3965_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3934_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3934_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
if (lean_obj_tag(v_a_3965_) == 11)
{
lean_dec_ref_known(v_a_3965_, 2);
lean_del_object(v___x_3967_);
v_a_3922_ = v___x_3930_;
v_snd_3923_ = v___x_3933_;
goto v___jp_3921_;
}
else
{
lean_object* v___x_3970_; 
lean_dec_ref(v___x_3933_);
lean_dec_ref(v_p_3914_);
lean_dec_ref(v_enter_3913_);
if (v_isShared_3968_ == 0)
{
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
return v___x_3970_;
}
}
}
}
}
v___jp_3921_:
{
size_t v___x_3924_; size_t v___x_3925_; 
v___x_3924_ = ((size_t)1ULL);
v___x_3925_ = lean_usize_add(v_i_3917_, v___x_3924_);
v_i_3917_ = v___x_3925_;
v_b_3918_ = v_a_3922_;
v___y_3919_ = v_snd_3923_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_enter_3913_ = stack[0].m_obj;
lean_object* v_p_3914_ = stack[1].m_obj;
lean_object* v_as_3915_ = stack[2].m_obj;
size_t v_sz_3916_ = stack[3].m_num;
size_t v_i_3917_ = stack[4].m_num;
lean_object* v_b_3918_ = stack[5].m_obj;
lean_object* v___y_3919_ = stack[6].m_obj;
lean_object* v_res_3973_;
v_res_3973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_3913_, v_p_3914_, v_as_3915_, v_sz_3916_, v_i_3917_, v_b_3918_, v___y_3919_);
stack->m_obj
 = v_res_3973_;
}
lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go(lean_object* v_enter_3974_, lean_object* v_p_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v___x_3978_; 
lean_inc_ref(v_enter_3974_);
lean_inc_ref(v_p_3975_);
v___x_3978_ = lean_apply_2(v_enter_3974_, v_p_3975_, lean_box(0));
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_4020_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_3981_ = v___x_3978_;
v_isShared_3982_ = v_isSharedCheck_4020_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3978_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_4020_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
uint8_t v___x_3983_; 
v___x_3983_ = lean_unbox(v_a_3979_);
lean_dec(v_a_3979_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3987_; 
lean_dec_ref(v_p_3975_);
lean_dec_ref(v_enter_3974_);
v___x_3984_ = lean_box(0);
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
lean_ctor_set(v___x_3985_, 1, v_a_3976_);
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 0, v___x_3985_);
v___x_3987_ = v___x_3981_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v___x_3985_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
else
{
lean_object* v___x_3989_; 
lean_del_object(v___x_3981_);
v___x_3989_ = lean_io_read_dir(v_p_3975_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v___x_3991_; size_t v_sz_3992_; size_t v___x_3993_; lean_object* v___x_3994_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref_known(v___x_3989_, 1);
v___x_3991_ = lean_box(0);
v_sz_3992_ = lean_array_size(v_a_3990_);
v___x_3993_ = ((size_t)0ULL);
v___x_3994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_3974_, v_p_3975_, v_a_3990_, v_sz_3992_, v___x_3993_, v___x_3991_, v_a_3976_);
lean_dec(v_a_3990_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4011_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_3997_ = v___x_3994_;
v_isShared_3998_ = v_isSharedCheck_4011_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3994_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4011_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v_snd_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4009_; 
v_snd_3999_ = lean_ctor_get(v_a_3995_, 1);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_a_3995_);
if (v_isSharedCheck_4009_ == 0)
{
lean_object* v_unused_4010_; 
v_unused_4010_ = lean_ctor_get(v_a_3995_, 0);
lean_dec(v_unused_4010_);
v___x_4001_ = v_a_3995_;
v_isShared_4002_ = v_isSharedCheck_4009_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_snd_3999_);
lean_dec(v_a_3995_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4009_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 0, v___x_3991_);
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_3991_);
lean_ctor_set(v_reuseFailAlloc_4008_, 1, v_snd_3999_);
v___x_4004_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
lean_object* v___x_4006_; 
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 0, v___x_4004_);
v___x_4006_ = v___x_3997_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_4004_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
}
else
{
return v___x_3994_;
}
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
lean_dec_ref(v_a_3976_);
lean_dec_ref(v_p_3975_);
lean_dec_ref(v_enter_3974_);
v_a_4012_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_3989_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_3989_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
}
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec_ref(v_a_3976_);
lean_dec_ref(v_p_3975_);
lean_dec_ref(v_enter_3974_);
v_a_4021_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_3978_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_3978_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_System_IO_0__System_FilePath_walkDir_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_enter_3974_ = stack[0].m_obj;
lean_object* v_p_3975_ = stack[1].m_obj;
lean_object* v_a_3976_ = stack[2].m_obj;
lean_object* v_res_4029_;
v_res_4029_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3974_, v_p_3975_, v_a_3976_);
stack->m_obj
 = v_res_4029_;
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go___boxed(lean_object* v_enter_4030_, lean_object* v_p_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_4030_, v_p_4031_, v_a_4032_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0___boxed(lean_object* v_enter_4035_, lean_object* v_p_4036_, lean_object* v_as_4037_, lean_object* v_sz_4038_, lean_object* v_i_4039_, lean_object* v_b_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
size_t v_sz_boxed_4043_; size_t v_i_boxed_4044_; lean_object* v_res_4045_; 
v_sz_boxed_4043_ = lean_unbox_usize(v_sz_4038_);
lean_dec(v_sz_4038_);
v_i_boxed_4044_ = lean_unbox_usize(v_i_4039_);
lean_dec(v_i_4039_);
v_res_4045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_4035_, v_p_4036_, v_as_4037_, v_sz_boxed_4043_, v_i_boxed_4044_, v_b_4040_, v___y_4041_);
lean_dec_ref(v_as_4037_);
return v_res_4045_;
}
}
lean_object* l_System_FilePath_walkDir(lean_object* v_p_4046_, lean_object* v_enter_4047_){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4049_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_4050_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_4047_, v_p_4046_, v___x_4049_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4059_; 
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4053_ = v___x_4050_;
v_isShared_4054_ = v_isSharedCheck_4059_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4050_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4059_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v_snd_4055_; lean_object* v___x_4057_; 
v_snd_4055_ = lean_ctor_get(v_a_4051_, 1);
lean_inc(v_snd_4055_);
lean_dec(v_a_4051_);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v_snd_4055_);
v___x_4057_ = v___x_4053_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_snd_4055_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
v_a_4060_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4050_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4050_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
LEAN_EXPORT void l_System_FilePath_walkDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_4046_ = stack[0].m_obj;
lean_object* v_enter_4047_ = stack[1].m_obj;
lean_object* v_res_4068_;
v_res_4068_ = l_System_FilePath_walkDir(v_p_4046_, v_enter_4047_);
stack->m_obj
 = v_res_4068_;
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir___boxed(lean_object* v_p_4069_, lean_object* v_enter_4070_, lean_object* v_a_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l_System_FilePath_walkDir(v_p_4069_, v_enter_4070_);
return v_res_4072_;
}
}
static lean_object* _init_l_IO_FS_readBinFile___closed__0(void){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = lean_unsigned_to_nat(0u);
v___x_4074_ = lean_mk_empty_byte_array(v___x_4073_);
return v___x_4074_;
}
}
lean_object* l_IO_FS_readBinFile(lean_object* v_fname_4075_){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = lean_io_metadata(v_fname_4075_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; uint64_t v_byteSize_4079_; size_t v___x_4080_; uint8_t v___x_4081_; lean_object* v___x_4082_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___x_4077_, 1);
v_byteSize_4079_ = lean_ctor_get_uint64(v_a_4078_, sizeof(void*)*2);
lean_dec(v_a_4078_);
v___x_4080_ = lean_uint64_to_usize(v_byteSize_4079_);
v___x_4081_ = 0;
v___x_4082_ = lean_io_prim_handle_mk(v_fname_4075_, v___x_4081_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; size_t v___x_4084_; uint8_t v___x_4085_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___x_4082_, 1);
v___x_4084_ = ((size_t)0ULL);
v___x_4085_ = lean_usize_dec_lt(v___x_4084_, v___x_4080_);
if (v___x_4085_ == 0)
{
lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4086_ = lean_obj_once(&l_IO_FS_readBinFile___closed__0, &l_IO_FS_readBinFile___closed__0_once, _init_l_IO_FS_readBinFile___closed__0);
v___x_4087_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_a_4083_, v___x_4086_);
lean_dec(v_a_4083_);
return v___x_4087_;
}
else
{
lean_object* v___x_4088_; 
v___x_4088_ = lean_io_prim_handle_read(v_a_4083_, v___x_4080_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v_a_4089_; lean_object* v___x_4090_; 
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref_known(v___x_4088_, 1);
v___x_4090_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_a_4083_, v_a_4089_);
lean_dec(v_a_4083_);
return v___x_4090_;
}
else
{
lean_dec(v_a_4083_);
return v___x_4088_;
}
}
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
v_a_4091_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4082_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4082_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
v_a_4099_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4077_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4077_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_readBinFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_fname_4075_ = stack[0].m_obj;
lean_object* v_res_4107_;
v_res_4107_ = l_IO_FS_readBinFile(v_fname_4075_);
stack->m_obj
 = v_res_4107_;
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object* v_fname_4108_, lean_object* v_a_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_IO_FS_readBinFile(v_fname_4108_);
lean_dec_ref(v_fname_4108_);
return v_res_4110_;
}
}
lean_object* l_IO_FS_readFile(lean_object* v_fname_4113_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = l_IO_FS_readBinFile(v_fname_4113_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4133_; 
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4118_ = v___x_4115_;
v_isShared_4119_ = v_isSharedCheck_4133_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4115_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4133_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
uint8_t v___x_4120_; 
v___x_4120_ = lean_string_validate_utf8(v_a_4116_);
if (v___x_4120_ == 0)
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4127_; 
lean_dec(v_a_4116_);
v___x_4121_ = ((lean_object*)(l_IO_FS_readFile___closed__0));
v___x_4122_ = lean_string_append(v___x_4121_, v_fname_4113_);
v___x_4123_ = ((lean_object*)(l_IO_FS_readFile___closed__1));
v___x_4124_ = lean_string_append(v___x_4122_, v___x_4123_);
v___x_4125_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set_tag(v___x_4118_, 1);
lean_ctor_set(v___x_4118_, 0, v___x_4125_);
v___x_4127_ = v___x_4118_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4125_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
else
{
lean_object* v___x_4129_; lean_object* v___x_4131_; 
v___x_4129_ = lean_string_from_utf8_unchecked(v_a_4116_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 0, v___x_4129_);
v___x_4131_ = v___x_4118_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
v_a_4134_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4115_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4115_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_readFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_fname_4113_ = stack[0].m_obj;
lean_object* v_res_4142_;
v_res_4142_ = l_IO_FS_readFile(v_fname_4113_);
stack->m_obj
 = v_res_4142_;
}
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object* v_fname_4143_, lean_object* v_a_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_IO_FS_readFile(v_fname_4143_);
lean_dec_ref(v_fname_4143_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0(lean_object* v_x_4146_){
_start:
{
lean_object* v_fst_4147_; 
v_fst_4147_ = lean_ctor_get(v_x_4146_, 0);
lean_inc(v_fst_4147_);
return v_fst_4147_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0___boxed(lean_object* v_x_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_IO_withStdin___redArg___lam__0(v_x_4148_);
lean_dec_ref(v_x_4148_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1(lean_object* v___x_4150_, lean_object* v_x_4151_){
_start:
{
lean_inc(v___x_4150_);
return v___x_4150_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1___boxed(lean_object* v___x_4152_, lean_object* v_x_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_IO_withStdin___redArg___lam__1(v___x_4152_, v_x_4153_);
lean_dec(v_x_4153_);
lean_dec(v___x_4152_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__2(lean_object* v_toFunctor_4155_, lean_object* v_inst_4156_, lean_object* v_inst_4157_, lean_object* v_x_4158_, lean_object* v___f_4159_, lean_object* v_prev_4160_){
_start:
{
lean_object* v_map_4161_; lean_object* v_mapConst_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___f_4167_; lean_object* v_y_4168_; lean_object* v___x_4169_; 
v_map_4161_ = lean_ctor_get(v_toFunctor_4155_, 0);
lean_inc(v_map_4161_);
v_mapConst_4162_ = lean_ctor_get(v_toFunctor_4155_, 1);
lean_inc(v_mapConst_4162_);
lean_dec_ref(v_toFunctor_4155_);
v___x_4163_ = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(v___x_4163_, 0, v_prev_4160_);
v___x_4164_ = lean_apply_2(v_inst_4156_, lean_box(0), v___x_4163_);
v___x_4165_ = lean_box(0);
v___x_4166_ = lean_apply_4(v_mapConst_4162_, lean_box(0), lean_box(0), v___x_4165_, v___x_4164_);
v___f_4167_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4167_, 0, v___x_4166_);
v_y_4168_ = lean_apply_4(v_inst_4157_, lean_box(0), lean_box(0), v_x_4158_, v___f_4167_);
v___x_4169_ = lean_apply_4(v_map_4161_, lean_box(0), lean_box(0), v___f_4159_, v_y_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg(lean_object* v_inst_4171_, lean_object* v_inst_4172_, lean_object* v_inst_4173_, lean_object* v_h_4174_, lean_object* v_x_4175_){
_start:
{
lean_object* v_toApplicative_4176_; lean_object* v_toBind_4177_; lean_object* v_toFunctor_4178_; lean_object* v___f_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___f_4182_; lean_object* v___x_4183_; 
v_toApplicative_4176_ = lean_ctor_get(v_inst_4171_, 0);
lean_inc_ref(v_toApplicative_4176_);
v_toBind_4177_ = lean_ctor_get(v_inst_4171_, 1);
lean_inc(v_toBind_4177_);
lean_dec_ref(v_inst_4171_);
v_toFunctor_4178_ = lean_ctor_get(v_toApplicative_4176_, 0);
lean_inc_ref(v_toFunctor_4178_);
lean_dec_ref(v_toApplicative_4176_);
v___f_4179_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4180_ = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(v___x_4180_, 0, v_h_4174_);
lean_inc(v_inst_4173_);
v___x_4181_ = lean_apply_2(v_inst_4173_, lean_box(0), v___x_4180_);
v___f_4182_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4182_, 0, v_toFunctor_4178_);
lean_closure_set(v___f_4182_, 1, v_inst_4173_);
lean_closure_set(v___f_4182_, 2, v_inst_4172_);
lean_closure_set(v___f_4182_, 3, v_x_4175_);
lean_closure_set(v___f_4182_, 4, v___f_4179_);
v___x_4183_ = lean_apply_4(v_toBind_4177_, lean_box(0), lean_box(0), v___x_4181_, v___f_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object* v_m_4184_, lean_object* v_00_u03b1_4185_, lean_object* v_inst_4186_, lean_object* v_inst_4187_, lean_object* v_inst_4188_, lean_object* v_h_4189_, lean_object* v_x_4190_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_IO_withStdin___redArg(v_inst_4186_, v_inst_4187_, v_inst_4188_, v_h_4189_, v_x_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg___lam__2(lean_object* v_toFunctor_4192_, lean_object* v_inst_4193_, lean_object* v_inst_4194_, lean_object* v_x_4195_, lean_object* v___f_4196_, lean_object* v_prev_4197_){
_start:
{
lean_object* v_map_4198_; lean_object* v_mapConst_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___f_4204_; lean_object* v_y_4205_; lean_object* v___x_4206_; 
v_map_4198_ = lean_ctor_get(v_toFunctor_4192_, 0);
lean_inc(v_map_4198_);
v_mapConst_4199_ = lean_ctor_get(v_toFunctor_4192_, 1);
lean_inc(v_mapConst_4199_);
lean_dec_ref(v_toFunctor_4192_);
v___x_4200_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_4200_, 0, v_prev_4197_);
v___x_4201_ = lean_apply_2(v_inst_4193_, lean_box(0), v___x_4200_);
v___x_4202_ = lean_box(0);
v___x_4203_ = lean_apply_4(v_mapConst_4199_, lean_box(0), lean_box(0), v___x_4202_, v___x_4201_);
v___f_4204_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4204_, 0, v___x_4203_);
v_y_4205_ = lean_apply_4(v_inst_4194_, lean_box(0), lean_box(0), v_x_4195_, v___f_4204_);
v___x_4206_ = lean_apply_4(v_map_4198_, lean_box(0), lean_box(0), v___f_4196_, v_y_4205_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg(lean_object* v_inst_4207_, lean_object* v_inst_4208_, lean_object* v_inst_4209_, lean_object* v_h_4210_, lean_object* v_x_4211_){
_start:
{
lean_object* v_toApplicative_4212_; lean_object* v_toBind_4213_; lean_object* v_toFunctor_4214_; lean_object* v___f_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___f_4218_; lean_object* v___x_4219_; 
v_toApplicative_4212_ = lean_ctor_get(v_inst_4207_, 0);
lean_inc_ref(v_toApplicative_4212_);
v_toBind_4213_ = lean_ctor_get(v_inst_4207_, 1);
lean_inc(v_toBind_4213_);
lean_dec_ref(v_inst_4207_);
v_toFunctor_4214_ = lean_ctor_get(v_toApplicative_4212_, 0);
lean_inc_ref(v_toFunctor_4214_);
lean_dec_ref(v_toApplicative_4212_);
v___f_4215_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4216_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_4216_, 0, v_h_4210_);
lean_inc(v_inst_4209_);
v___x_4217_ = lean_apply_2(v_inst_4209_, lean_box(0), v___x_4216_);
v___f_4218_ = lean_alloc_closure((void*)(l_IO_withStdout___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4218_, 0, v_toFunctor_4214_);
lean_closure_set(v___f_4218_, 1, v_inst_4209_);
lean_closure_set(v___f_4218_, 2, v_inst_4208_);
lean_closure_set(v___f_4218_, 3, v_x_4211_);
lean_closure_set(v___f_4218_, 4, v___f_4215_);
v___x_4219_ = lean_apply_4(v_toBind_4213_, lean_box(0), lean_box(0), v___x_4217_, v___f_4218_);
return v___x_4219_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object* v_m_4220_, lean_object* v_00_u03b1_4221_, lean_object* v_inst_4222_, lean_object* v_inst_4223_, lean_object* v_inst_4224_, lean_object* v_h_4225_, lean_object* v_x_4226_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l_IO_withStdout___redArg(v_inst_4222_, v_inst_4223_, v_inst_4224_, v_h_4225_, v_x_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg___lam__2(lean_object* v_toFunctor_4228_, lean_object* v_inst_4229_, lean_object* v_inst_4230_, lean_object* v_x_4231_, lean_object* v___f_4232_, lean_object* v_prev_4233_){
_start:
{
lean_object* v_map_4234_; lean_object* v_mapConst_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___f_4240_; lean_object* v_y_4241_; lean_object* v___x_4242_; 
v_map_4234_ = lean_ctor_get(v_toFunctor_4228_, 0);
lean_inc(v_map_4234_);
v_mapConst_4235_ = lean_ctor_get(v_toFunctor_4228_, 1);
lean_inc(v_mapConst_4235_);
lean_dec_ref(v_toFunctor_4228_);
v___x_4236_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_4236_, 0, v_prev_4233_);
v___x_4237_ = lean_apply_2(v_inst_4229_, lean_box(0), v___x_4236_);
v___x_4238_ = lean_box(0);
v___x_4239_ = lean_apply_4(v_mapConst_4235_, lean_box(0), lean_box(0), v___x_4238_, v___x_4237_);
v___f_4240_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4240_, 0, v___x_4239_);
v_y_4241_ = lean_apply_4(v_inst_4230_, lean_box(0), lean_box(0), v_x_4231_, v___f_4240_);
v___x_4242_ = lean_apply_4(v_map_4234_, lean_box(0), lean_box(0), v___f_4232_, v_y_4241_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg(lean_object* v_inst_4243_, lean_object* v_inst_4244_, lean_object* v_inst_4245_, lean_object* v_h_4246_, lean_object* v_x_4247_){
_start:
{
lean_object* v_toApplicative_4248_; lean_object* v_toBind_4249_; lean_object* v_toFunctor_4250_; lean_object* v___f_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___f_4254_; lean_object* v___x_4255_; 
v_toApplicative_4248_ = lean_ctor_get(v_inst_4243_, 0);
lean_inc_ref(v_toApplicative_4248_);
v_toBind_4249_ = lean_ctor_get(v_inst_4243_, 1);
lean_inc(v_toBind_4249_);
lean_dec_ref(v_inst_4243_);
v_toFunctor_4250_ = lean_ctor_get(v_toApplicative_4248_, 0);
lean_inc_ref(v_toFunctor_4250_);
lean_dec_ref(v_toApplicative_4248_);
v___f_4251_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4252_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_4252_, 0, v_h_4246_);
lean_inc(v_inst_4245_);
v___x_4253_ = lean_apply_2(v_inst_4245_, lean_box(0), v___x_4252_);
v___f_4254_ = lean_alloc_closure((void*)(l_IO_withStderr___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4254_, 0, v_toFunctor_4250_);
lean_closure_set(v___f_4254_, 1, v_inst_4245_);
lean_closure_set(v___f_4254_, 2, v_inst_4244_);
lean_closure_set(v___f_4254_, 3, v_x_4247_);
lean_closure_set(v___f_4254_, 4, v___f_4251_);
v___x_4255_ = lean_apply_4(v_toBind_4249_, lean_box(0), lean_box(0), v___x_4253_, v___f_4254_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object* v_m_4256_, lean_object* v_00_u03b1_4257_, lean_object* v_inst_4258_, lean_object* v_inst_4259_, lean_object* v_inst_4260_, lean_object* v_h_4261_, lean_object* v_x_4262_){
_start:
{
lean_object* v___x_4263_; 
v___x_4263_ = l_IO_withStderr___redArg(v_inst_4258_, v_inst_4259_, v_inst_4260_, v_h_4261_, v_x_4262_);
return v___x_4263_;
}
}
lean_object* l_IO_print___redArg(lean_object* v_inst_4264_, lean_object* v_s_4265_){
_start:
{
lean_object* v___x_4267_; lean_object* v_putStr_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4267_ = lean_get_stdout();
v_putStr_4268_ = lean_ctor_get(v___x_4267_, 4);
lean_inc_ref(v_putStr_4268_);
lean_dec_ref(v___x_4267_);
v___x_4269_ = lean_apply_1(v_inst_4264_, v_s_4265_);
v___x_4270_ = lean_apply_2(v_putStr_4268_, v___x_4269_, lean_box(0));
return v___x_4270_;
}
}
LEAN_EXPORT void l_IO_print___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4264_ = stack[0].m_obj;
lean_object* v_s_4265_ = stack[1].m_obj;
lean_object* v_res_4271_;
v_res_4271_ = l_IO_print___redArg(v_inst_4264_, v_s_4265_);
stack->m_obj
 = v_res_4271_;
}
LEAN_EXPORT lean_object* l_IO_print___redArg___boxed(lean_object* v_inst_4272_, lean_object* v_s_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_IO_print___redArg(v_inst_4272_, v_s_4273_);
return v_res_4275_;
}
}
lean_object* l_IO_print(lean_object* v_00_u03b1_4276_, lean_object* v_inst_4277_, lean_object* v_s_4278_){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l_IO_print___redArg(v_inst_4277_, v_s_4278_);
return v___x_4280_;
}
}
LEAN_EXPORT void l_IO_print_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4277_ = stack[1].m_obj;
lean_object* v_s_4278_ = stack[2].m_obj;
lean_object* v_res_4281_;
v_res_4281_ = l_IO_print(lean_box(0), v_inst_4277_, v_s_4278_);
stack->m_obj
 = v_res_4281_;
}
LEAN_EXPORT lean_object* l_IO_print___boxed(lean_object* v_00_u03b1_4282_, lean_object* v_inst_4283_, lean_object* v_s_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_IO_print(v_00_u03b1_4282_, v_inst_4283_, v_s_4284_);
return v_res_4286_;
}
}
lean_object* l_IO_println___redArg(lean_object* v_inst_4288_, lean_object* v_s_4289_){
_start:
{
lean_object* v___f_4291_; lean_object* v___x_4292_; uint32_t v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___f_4291_ = ((lean_object*)(l_IO_println___redArg___closed__0));
v___x_4292_ = lean_apply_1(v_inst_4288_, v_s_4289_);
v___x_4293_ = 10;
v___x_4294_ = lean_string_push(v___x_4292_, v___x_4293_);
v___x_4295_ = l_IO_print___redArg(v___f_4291_, v___x_4294_);
return v___x_4295_;
}
}
LEAN_EXPORT void l_IO_println___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4288_ = stack[0].m_obj;
lean_object* v_s_4289_ = stack[1].m_obj;
lean_object* v_res_4296_;
v_res_4296_ = l_IO_println___redArg(v_inst_4288_, v_s_4289_);
stack->m_obj
 = v_res_4296_;
}
LEAN_EXPORT lean_object* l_IO_println___redArg___boxed(lean_object* v_inst_4297_, lean_object* v_s_4298_, lean_object* v_a_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_IO_println___redArg(v_inst_4297_, v_s_4298_);
return v_res_4300_;
}
}
lean_object* l_IO_println(lean_object* v_00_u03b1_4301_, lean_object* v_inst_4302_, lean_object* v_s_4303_){
_start:
{
lean_object* v___x_4305_; 
v___x_4305_ = l_IO_println___redArg(v_inst_4302_, v_s_4303_);
return v___x_4305_;
}
}
LEAN_EXPORT void l_IO_println_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4302_ = stack[1].m_obj;
lean_object* v_s_4303_ = stack[2].m_obj;
lean_object* v_res_4306_;
v_res_4306_ = l_IO_println(lean_box(0), v_inst_4302_, v_s_4303_);
stack->m_obj
 = v_res_4306_;
}
LEAN_EXPORT lean_object* l_IO_println___boxed(lean_object* v_00_u03b1_4307_, lean_object* v_inst_4308_, lean_object* v_s_4309_, lean_object* v_a_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_IO_println(v_00_u03b1_4307_, v_inst_4308_, v_s_4309_);
return v_res_4311_;
}
}
lean_object* l_IO_eprint___redArg(lean_object* v_inst_4312_, lean_object* v_s_4313_){
_start:
{
lean_object* v___x_4315_; lean_object* v_putStr_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
v___x_4315_ = lean_get_stderr();
v_putStr_4316_ = lean_ctor_get(v___x_4315_, 4);
lean_inc_ref(v_putStr_4316_);
lean_dec_ref(v___x_4315_);
v___x_4317_ = lean_apply_1(v_inst_4312_, v_s_4313_);
v___x_4318_ = lean_apply_2(v_putStr_4316_, v___x_4317_, lean_box(0));
return v___x_4318_;
}
}
LEAN_EXPORT void l_IO_eprint___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4312_ = stack[0].m_obj;
lean_object* v_s_4313_ = stack[1].m_obj;
lean_object* v_res_4319_;
v_res_4319_ = l_IO_eprint___redArg(v_inst_4312_, v_s_4313_);
stack->m_obj
 = v_res_4319_;
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg___boxed(lean_object* v_inst_4320_, lean_object* v_s_4321_, lean_object* v_a_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l_IO_eprint___redArg(v_inst_4320_, v_s_4321_);
return v_res_4323_;
}
}
lean_object* l_IO_eprint(lean_object* v_00_u03b1_4324_, lean_object* v_inst_4325_, lean_object* v_s_4326_){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = l_IO_eprint___redArg(v_inst_4325_, v_s_4326_);
return v___x_4328_;
}
}
LEAN_EXPORT void l_IO_eprint_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4325_ = stack[1].m_obj;
lean_object* v_s_4326_ = stack[2].m_obj;
lean_object* v_res_4329_;
v_res_4329_ = l_IO_eprint(lean_box(0), v_inst_4325_, v_s_4326_);
stack->m_obj
 = v_res_4329_;
}
LEAN_EXPORT lean_object* l_IO_eprint___boxed(lean_object* v_00_u03b1_4330_, lean_object* v_inst_4331_, lean_object* v_s_4332_, lean_object* v_a_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = l_IO_eprint(v_00_u03b1_4330_, v_inst_4331_, v_s_4332_);
return v_res_4334_;
}
}
lean_object* l_IO_eprintln___redArg(lean_object* v_inst_4335_, lean_object* v_s_4336_){
_start:
{
lean_object* v___f_4338_; lean_object* v___x_4339_; uint32_t v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___f_4338_ = ((lean_object*)(l_IO_println___redArg___closed__0));
v___x_4339_ = lean_apply_1(v_inst_4335_, v_s_4336_);
v___x_4340_ = 10;
v___x_4341_ = lean_string_push(v___x_4339_, v___x_4340_);
v___x_4342_ = l_IO_eprint___redArg(v___f_4338_, v___x_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT void l_IO_eprintln___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4335_ = stack[0].m_obj;
lean_object* v_s_4336_ = stack[1].m_obj;
lean_object* v_res_4343_;
v_res_4343_ = l_IO_eprintln___redArg(v_inst_4335_, v_s_4336_);
stack->m_obj
 = v_res_4343_;
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg___boxed(lean_object* v_inst_4344_, lean_object* v_s_4345_, lean_object* v_a_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l_IO_eprintln___redArg(v_inst_4344_, v_s_4345_);
return v_res_4347_;
}
}
lean_object* l_IO_eprintln(lean_object* v_00_u03b1_4348_, lean_object* v_inst_4349_, lean_object* v_s_4350_){
_start:
{
lean_object* v___x_4352_; 
v___x_4352_ = l_IO_eprintln___redArg(v_inst_4349_, v_s_4350_);
return v___x_4352_;
}
}
LEAN_EXPORT void l_IO_eprintln_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4349_ = stack[1].m_obj;
lean_object* v_s_4350_ = stack[2].m_obj;
lean_object* v_res_4353_;
v_res_4353_ = l_IO_eprintln(lean_box(0), v_inst_4349_, v_s_4350_);
stack->m_obj
 = v_res_4353_;
}
LEAN_EXPORT lean_object* l_IO_eprintln___boxed(lean_object* v_00_u03b1_4354_, lean_object* v_inst_4355_, lean_object* v_s_4356_, lean_object* v_a_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l_IO_eprintln(v_00_u03b1_4354_, v_inst_4355_, v_s_4356_);
return v_res_4358_;
}
}
lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object* v_s_4359_){
_start:
{
lean_object* v___x_4361_; lean_object* v_putStr_4362_; lean_object* v___x_4363_; 
v___x_4361_ = lean_get_stderr();
v_putStr_4362_ = lean_ctor_get(v___x_4361_, 4);
lean_inc_ref(v_putStr_4362_);
lean_dec_ref(v___x_4361_);
v___x_4363_ = lean_apply_2(v_putStr_4362_, v_s_4359_, lean_box(0));
return v___x_4363_;
}
}
LEAN_EXPORT void l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4359_ = stack[0].m_obj;
lean_object* v_res_4364_;
v_res_4364_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_4359_);
stack->m_obj
 = v_res_4364_;
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0___boxed(lean_object* v_s_4365_, lean_object* v_a_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_4365_);
return v_res_4367_;
}
}
lean_object* lean_io_eprint(lean_object* v_s_4368_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_4368_);
return v___x_4370_;
}
}
LEAN_EXPORT void lean_io_eprint_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4368_ = stack[0].m_obj;
lean_object* v_res_4371_;
v_res_4371_ = lean_io_eprint(v_s_4368_);
stack->m_obj
 = v_res_4371_;
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintAux___boxed(lean_object* v_s_4372_, lean_object* v_a_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = lean_io_eprint(v_s_4372_);
return v_res_4374_;
}
}
lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object* v_s_4375_){
_start:
{
uint32_t v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4377_ = 10;
v___x_4378_ = lean_string_push(v_s_4375_, v___x_4377_);
v___x_4379_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v___x_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT void l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4375_ = stack[0].m_obj;
lean_object* v_res_4380_;
v_res_4380_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_4375_);
stack->m_obj
 = v_res_4380_;
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0___boxed(lean_object* v_s_4381_, lean_object* v_a_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_4381_);
return v_res_4383_;
}
}
lean_object* lean_io_eprintln(lean_object* v_s_4384_){
_start:
{
lean_object* v___x_4386_; 
v___x_4386_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_4384_);
return v___x_4386_;
}
}
LEAN_EXPORT void lean_io_eprintln_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4384_ = stack[0].m_obj;
lean_object* v_res_4387_;
v_res_4387_ = lean_io_eprintln(v_s_4384_);
stack->m_obj
 = v_res_4387_;
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintlnAux___boxed(lean_object* v_s_4388_, lean_object* v_a_4389_){
_start:
{
lean_object* v_res_4390_; 
v_res_4390_ = lean_io_eprintln(v_s_4388_);
return v_res_4390_;
}
}
lean_object* l_IO_appDir(){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = lean_io_app_path();
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4410_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4397_ = v___x_4394_;
v_isShared_4398_ = v_isSharedCheck_4410_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4394_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4410_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4399_; 
lean_inc(v_a_4395_);
v___x_4399_ = l_System_FilePath_parent(v_a_4395_);
if (lean_obj_tag(v___x_4399_) == 1)
{
lean_object* v_val_4400_; lean_object* v___x_4401_; 
lean_del_object(v___x_4397_);
lean_dec(v_a_4395_);
v_val_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_val_4400_);
lean_dec_ref_known(v___x_4399_, 1);
v___x_4401_ = lean_io_realpath(v_val_4400_);
return v___x_4401_;
}
else
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4408_; 
lean_dec(v___x_4399_);
v___x_4402_ = ((lean_object*)(l_IO_appDir___closed__0));
v___x_4403_ = lean_string_append(v___x_4402_, v_a_4395_);
lean_dec(v_a_4395_);
v___x_4404_ = ((lean_object*)(l_IO_appDir___closed__1));
v___x_4405_ = lean_string_append(v___x_4403_, v___x_4404_);
v___x_4406_ = lean_mk_io_user_error(v___x_4405_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set_tag(v___x_4397_, 1);
lean_ctor_set(v___x_4397_, 0, v___x_4406_);
v___x_4408_ = v___x_4397_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4406_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
else
{
return v___x_4394_;
}
}
}
LEAN_EXPORT void l_IO_appDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4411_;
v_res_4411_ = l_IO_appDir();
stack->m_obj
 = v_res_4411_;
}
LEAN_EXPORT lean_object* l_IO_appDir___boxed(lean_object* v_a_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_IO_appDir();
return v_res_4413_;
}
}
lean_object* l_IO_FS_createDirAll(lean_object* v_p_4414_){
_start:
{
uint8_t v___x_4431_; 
v___x_4431_ = l_System_FilePath_isDir(v_p_4414_);
if (v___x_4431_ == 0)
{
lean_object* v___x_4432_; 
lean_inc_ref(v_p_4414_);
v___x_4432_ = l_System_FilePath_parent(v_p_4414_);
if (lean_obj_tag(v___x_4432_) == 1)
{
lean_object* v_val_4433_; lean_object* v___x_4434_; 
v_val_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc(v_val_4433_);
lean_dec_ref_known(v___x_4432_, 1);
v___x_4434_ = l_IO_FS_createDirAll(v_val_4433_);
if (lean_obj_tag(v___x_4434_) == 0)
{
lean_dec_ref_known(v___x_4434_, 1);
goto v___jp_4416_;
}
else
{
lean_dec_ref(v_p_4414_);
return v___x_4434_;
}
}
else
{
lean_dec(v___x_4432_);
goto v___jp_4416_;
}
}
else
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
lean_dec_ref(v_p_4414_);
v___x_4435_ = lean_box(0);
v___x_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4435_);
return v___x_4436_;
}
v___jp_4416_:
{
lean_object* v___x_4417_; 
v___x_4417_ = lean_io_create_dir(v_p_4414_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_dec_ref(v_p_4414_);
return v___x_4417_;
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4430_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4420_ = v___x_4417_;
v_isShared_4421_ = v_isSharedCheck_4430_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4417_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4430_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
uint8_t v___x_4422_; 
v___x_4422_ = l_System_FilePath_isDir(v_p_4414_);
lean_dec_ref(v_p_4414_);
if (v___x_4422_ == 0)
{
lean_object* v___x_4424_; 
if (v_isShared_4421_ == 0)
{
v___x_4424_ = v___x_4420_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4418_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
else
{
lean_object* v___x_4426_; lean_object* v___x_4428_; 
lean_dec(v_a_4418_);
v___x_4426_ = lean_box(0);
if (v_isShared_4421_ == 0)
{
lean_ctor_set_tag(v___x_4420_, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4426_);
v___x_4428_ = v___x_4420_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4426_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_createDirAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_4414_ = stack[0].m_obj;
lean_object* v_res_4437_;
v_res_4437_ = l_IO_FS_createDirAll(v_p_4414_);
stack->m_obj
 = v_res_4437_;
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object* v_p_4438_, lean_object* v_a_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l_IO_FS_createDirAll(v_p_4438_);
return v_res_4440_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(lean_object* v_as_4441_, size_t v_sz_4442_, size_t v_i_4443_, lean_object* v_b_4444_){
_start:
{
lean_object* v_a_4447_; uint8_t v___x_4451_; 
v___x_4451_ = lean_usize_dec_lt(v_i_4443_, v_sz_4442_);
if (v___x_4451_ == 0)
{
lean_object* v___x_4452_; 
v___x_4452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4452_, 0, v_b_4444_);
return v___x_4452_;
}
else
{
lean_object* v___x_4453_; lean_object* v_a_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4453_ = lean_box(0);
v_a_4454_ = lean_array_uget_borrowed(v_as_4441_, v_i_4443_);
lean_inc(v_a_4454_);
v___x_4455_ = l_IO_FS_DirEntry_path(v_a_4454_);
v___x_4456_ = lean_io_symlink_metadata(v___x_4455_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v_a_4457_; uint8_t v_type_4458_; uint8_t v___x_4459_; uint8_t v___x_4460_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_a_4457_);
lean_dec_ref_known(v___x_4456_, 1);
v_type_4458_ = lean_ctor_get_uint8(v_a_4457_, sizeof(void*)*2 + 16);
lean_dec(v_a_4457_);
v___x_4459_ = 0;
v___x_4460_ = l_IO_FS_instBEqFileType_beq(v_type_4458_, v___x_4459_);
if (v___x_4460_ == 0)
{
lean_object* v___x_4461_; 
v___x_4461_ = lean_io_remove_file(v___x_4455_);
lean_dec_ref(v___x_4455_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_dec_ref_known(v___x_4461_, 1);
v_a_4447_ = v___x_4453_;
goto v___jp_4446_;
}
else
{
return v___x_4461_;
}
}
else
{
lean_object* v___x_4462_; 
v___x_4462_ = l_IO_FS_removeDirAll(v___x_4455_);
lean_dec_ref(v___x_4455_);
if (lean_obj_tag(v___x_4462_) == 0)
{
lean_dec_ref_known(v___x_4462_, 1);
v_a_4447_ = v___x_4453_;
goto v___jp_4446_;
}
else
{
return v___x_4462_;
}
}
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_dec_ref(v___x_4455_);
v_a_4463_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4456_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4456_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
v___jp_4446_:
{
size_t v___x_4448_; size_t v___x_4449_; 
v___x_4448_ = ((size_t)1ULL);
v___x_4449_ = lean_usize_add(v_i_4443_, v___x_4448_);
v_i_4443_ = v___x_4449_;
v_b_4444_ = v_a_4447_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4441_ = stack[0].m_obj;
size_t v_sz_4442_ = stack[1].m_num;
size_t v_i_4443_ = stack[2].m_num;
lean_object* v_b_4444_ = stack[3].m_obj;
lean_object* v_res_4471_;
v_res_4471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_as_4441_, v_sz_4442_, v_i_4443_, v_b_4444_);
stack->m_obj
 = v_res_4471_;
}
lean_object* l_IO_FS_removeDirAll(lean_object* v_p_4472_){
_start:
{
lean_object* v___x_4474_; 
v___x_4474_ = lean_io_read_dir(v_p_4472_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v_a_4475_; lean_object* v___x_4476_; size_t v_sz_4477_; size_t v___x_4478_; lean_object* v___x_4479_; 
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4475_);
lean_dec_ref_known(v___x_4474_, 1);
v___x_4476_ = lean_box(0);
v_sz_4477_ = lean_array_size(v_a_4475_);
v___x_4478_ = ((size_t)0ULL);
v___x_4479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_a_4475_, v_sz_4477_, v___x_4478_, v___x_4476_);
lean_dec(v_a_4475_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v___x_4480_; 
lean_dec_ref_known(v___x_4479_, 1);
v___x_4480_ = lean_io_remove_dir(v_p_4472_);
return v___x_4480_;
}
else
{
return v___x_4479_;
}
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
v_a_4481_ = lean_ctor_get(v___x_4474_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4474_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4474_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4474_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_removeDirAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_4472_ = stack[0].m_obj;
lean_object* v_res_4489_;
v_res_4489_ = l_IO_FS_removeDirAll(v_p_4472_);
stack->m_obj
 = v_res_4489_;
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object* v_p_4490_, lean_object* v_a_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l_IO_FS_removeDirAll(v_p_4490_);
lean_dec_ref(v_p_4490_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0___boxed(lean_object* v_as_4493_, lean_object* v_sz_4494_, lean_object* v_i_4495_, lean_object* v_b_4496_, lean_object* v___y_4497_){
_start:
{
size_t v_sz_boxed_4498_; size_t v_i_boxed_4499_; lean_object* v_res_4500_; 
v_sz_boxed_4498_ = lean_unbox_usize(v_sz_4494_);
lean_dec(v_sz_4494_);
v_i_boxed_4499_ = lean_unbox_usize(v_i_4495_);
lean_dec(v_i_4495_);
v_res_4500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_as_4493_, v_sz_boxed_4498_, v_i_boxed_4499_, v_b_4496_);
lean_dec_ref(v_as_4493_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg___lam__2(lean_object* v_toFunctor_4501_, lean_object* v_f_4502_, lean_object* v_inst_4503_, lean_object* v_inst_4504_, lean_object* v___f_4505_, lean_object* v_____x_4506_){
_start:
{
lean_object* v_fst_4507_; lean_object* v_snd_4508_; lean_object* v_map_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___f_4513_; lean_object* v_y_4514_; lean_object* v___x_4515_; 
v_fst_4507_ = lean_ctor_get(v_____x_4506_, 0);
lean_inc(v_fst_4507_);
v_snd_4508_ = lean_ctor_get(v_____x_4506_, 1);
lean_inc_n(v_snd_4508_, 2);
lean_dec_ref(v_____x_4506_);
v_map_4509_ = lean_ctor_get(v_toFunctor_4501_, 0);
lean_inc(v_map_4509_);
lean_dec_ref(v_toFunctor_4501_);
v___x_4510_ = lean_apply_2(v_f_4502_, v_fst_4507_, v_snd_4508_);
v___x_4511_ = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(v___x_4511_, 0, v_snd_4508_);
v___x_4512_ = lean_apply_2(v_inst_4503_, lean_box(0), v___x_4511_);
v___f_4513_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4513_, 0, v___x_4512_);
v_y_4514_ = lean_apply_4(v_inst_4504_, lean_box(0), lean_box(0), v___x_4510_, v___f_4513_);
v___x_4515_ = lean_apply_4(v_map_4509_, lean_box(0), lean_box(0), v___f_4505_, v_y_4514_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg(lean_object* v_inst_4517_, lean_object* v_inst_4518_, lean_object* v_inst_4519_, lean_object* v_f_4520_){
_start:
{
lean_object* v_toApplicative_4521_; lean_object* v_toBind_4522_; lean_object* v_toFunctor_4523_; lean_object* v___f_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___f_4527_; lean_object* v___x_4528_; 
v_toApplicative_4521_ = lean_ctor_get(v_inst_4517_, 0);
lean_inc_ref(v_toApplicative_4521_);
v_toBind_4522_ = lean_ctor_get(v_inst_4517_, 1);
lean_inc(v_toBind_4522_);
lean_dec_ref(v_inst_4517_);
v_toFunctor_4523_ = lean_ctor_get(v_toApplicative_4521_, 0);
lean_inc_ref(v_toFunctor_4523_);
lean_dec_ref(v_toApplicative_4521_);
v___f_4524_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4525_ = ((lean_object*)(l_IO_FS_withTempFile___redArg___closed__0));
lean_inc(v_inst_4519_);
v___x_4526_ = lean_apply_2(v_inst_4519_, lean_box(0), v___x_4525_);
v___f_4527_ = lean_alloc_closure((void*)(l_IO_FS_withTempFile___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4527_, 0, v_toFunctor_4523_);
lean_closure_set(v___f_4527_, 1, v_f_4520_);
lean_closure_set(v___f_4527_, 2, v_inst_4519_);
lean_closure_set(v___f_4527_, 3, v_inst_4518_);
lean_closure_set(v___f_4527_, 4, v___f_4524_);
v___x_4528_ = lean_apply_4(v_toBind_4522_, lean_box(0), lean_box(0), v___x_4526_, v___f_4527_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile(lean_object* v_m_4529_, lean_object* v_00_u03b1_4530_, lean_object* v_inst_4531_, lean_object* v_inst_4532_, lean_object* v_inst_4533_, lean_object* v_f_4534_){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = l_IO_FS_withTempFile___redArg(v_inst_4531_, v_inst_4532_, v_inst_4533_, v_f_4534_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg___lam__2(lean_object* v_toFunctor_4536_, lean_object* v_f_4537_, lean_object* v_inst_4538_, lean_object* v_inst_4539_, lean_object* v___f_4540_, lean_object* v_path_4541_){
_start:
{
lean_object* v_map_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___f_4546_; lean_object* v_y_4547_; lean_object* v___x_4548_; 
v_map_4542_ = lean_ctor_get(v_toFunctor_4536_, 0);
lean_inc(v_map_4542_);
lean_dec_ref(v_toFunctor_4536_);
lean_inc_ref(v_path_4541_);
v___x_4543_ = lean_apply_1(v_f_4537_, v_path_4541_);
v___x_4544_ = lean_alloc_closure((void*)(l_IO_FS_removeDirAll___boxed), 2, 1);
lean_closure_set(v___x_4544_, 0, v_path_4541_);
v___x_4545_ = lean_apply_2(v_inst_4538_, lean_box(0), v___x_4544_);
v___f_4546_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4546_, 0, v___x_4545_);
v_y_4547_ = lean_apply_4(v_inst_4539_, lean_box(0), lean_box(0), v___x_4543_, v___f_4546_);
v___x_4548_ = lean_apply_4(v_map_4542_, lean_box(0), lean_box(0), v___f_4540_, v_y_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg(lean_object* v_inst_4550_, lean_object* v_inst_4551_, lean_object* v_inst_4552_, lean_object* v_f_4553_){
_start:
{
lean_object* v_toApplicative_4554_; lean_object* v_toBind_4555_; lean_object* v_toFunctor_4556_; lean_object* v___f_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___f_4560_; lean_object* v___x_4561_; 
v_toApplicative_4554_ = lean_ctor_get(v_inst_4550_, 0);
lean_inc_ref(v_toApplicative_4554_);
v_toBind_4555_ = lean_ctor_get(v_inst_4550_, 1);
lean_inc(v_toBind_4555_);
lean_dec_ref(v_inst_4550_);
v_toFunctor_4556_ = lean_ctor_get(v_toApplicative_4554_, 0);
lean_inc_ref(v_toFunctor_4556_);
lean_dec_ref(v_toApplicative_4554_);
v___f_4557_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4558_ = ((lean_object*)(l_IO_FS_withTempDir___redArg___closed__0));
lean_inc(v_inst_4552_);
v___x_4559_ = lean_apply_2(v_inst_4552_, lean_box(0), v___x_4558_);
v___f_4560_ = lean_alloc_closure((void*)(l_IO_FS_withTempDir___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4560_, 0, v_toFunctor_4556_);
lean_closure_set(v___f_4560_, 1, v_f_4553_);
lean_closure_set(v___f_4560_, 2, v_inst_4552_);
lean_closure_set(v___f_4560_, 3, v_inst_4551_);
lean_closure_set(v___f_4560_, 4, v___f_4557_);
v___x_4561_ = lean_apply_4(v_toBind_4555_, lean_box(0), lean_box(0), v___x_4559_, v___f_4560_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir(lean_object* v_m_4562_, lean_object* v_00_u03b1_4563_, lean_object* v_inst_4564_, lean_object* v_inst_4565_, lean_object* v_inst_4566_, lean_object* v_f_4567_){
_start:
{
lean_object* v___x_4568_; 
v___x_4568_ = l_IO_FS_withTempDir___redArg(v_inst_4564_, v_inst_4565_, v_inst_4566_, v_f_4567_);
return v___x_4568_;
}
}
LEAN_EXPORT void l_IO_Process_getCurrentDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4570_;
v_res_4570_ = lean_io_process_get_current_dir();
stack->m_obj
 = v_res_4570_;
}
LEAN_EXPORT lean_object* l_IO_Process_getCurrentDir___boxed(lean_object* v_a_00___x40___internal___hyg_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = lean_io_process_get_current_dir();
return v_res_4572_;
}
}
LEAN_EXPORT void l_IO_Process_setCurrentDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_4573_ = stack[0].m_obj;
lean_object* v_res_4575_;
v_res_4575_ = lean_io_process_set_current_dir(v_path_4573_);
stack->m_obj
 = v_res_4575_;
}
LEAN_EXPORT lean_object* l_IO_Process_setCurrentDir___boxed(lean_object* v_path_4576_, lean_object* v_a_00___x40___internal___hyg_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = lean_io_process_set_current_dir(v_path_4576_);
lean_dec_ref(v_path_4576_);
return v_res_4578_;
}
}
LEAN_EXPORT void l_IO_Process_getPID_0interp(lean_interpreter_value* stack)
{
uint32_t v_res_4580_;
v_res_4580_ = lean_io_process_get_pid();
stack->m_num = v_res_4580_;
}
LEAN_EXPORT lean_object* l_IO_Process_getPID___boxed(lean_object* v_a_00___x40___internal___hyg_4581_){
_start:
{
uint32_t v_res_4582_; lean_object* v_r_4583_; 
v_res_4582_ = lean_io_process_get_pid();
v_r_4583_ = lean_box_uint32(v_res_4582_);
return v_r_4583_;
}
}
lean_object* l_IO_Process_Stdio_ctorIdx___impl(uint8_t v_x_4584_){
_start:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4585_ = lean_box(v_x_4584_);
v___x_4586_ = lean_obj_tag_nat(v___x_4585_);
lean_dec(v___x_4585_);
return v___x_4586_;
}
}
LEAN_EXPORT void l_IO_Process_Stdio_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_4584_ = stack[0].m_num;
lean_object* v_res_4587_;
v_res_4587_ = l_IO_Process_Stdio_ctorIdx___impl(v_x_4584_);
stack->m_obj
 = v_res_4587_;
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx___impl___boxed(lean_object* v_x_4588_){
_start:
{
uint8_t v_x_4__boxed_4589_; lean_object* v_res_4590_; 
v_x_4__boxed_4589_ = lean_unbox(v_x_4588_);
v_res_4590_ = l_IO_Process_Stdio_ctorIdx___impl(v_x_4__boxed_4589_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg(lean_object* v_k_4591_){
_start:
{
lean_inc(v_k_4591_);
return v_k_4591_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg___boxed(lean_object* v_k_4592_){
_start:
{
lean_object* v_res_4593_; 
v_res_4593_ = l_IO_Process_Stdio_ctorElim___redArg(v_k_4592_);
lean_dec(v_k_4592_);
return v_res_4593_;
}
}
lean_object* l_IO_Process_Stdio_ctorElim(lean_object* v_motive_4594_, lean_object* v_ctorIdx_4595_, uint8_t v_t_4596_, lean_object* v_h_4597_, lean_object* v_k_4598_){
_start:
{
lean_inc(v_k_4598_);
return v_k_4598_;
}
}
LEAN_EXPORT void l_IO_Process_Stdio_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_4595_ = stack[1].m_obj;
uint8_t v_t_4596_ = stack[2].m_num;
lean_object* v_k_4598_ = stack[4].m_obj;
lean_object* v_res_4599_;
v_res_4599_ = l_IO_Process_Stdio_ctorElim(lean_box(0), v_ctorIdx_4595_, v_t_4596_, lean_box(0), v_k_4598_);
stack->m_obj
 = v_res_4599_;
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___boxed(lean_object* v_motive_4600_, lean_object* v_ctorIdx_4601_, lean_object* v_t_4602_, lean_object* v_h_4603_, lean_object* v_k_4604_){
_start:
{
uint8_t v_t_boxed_4605_; lean_object* v_res_4606_; 
v_t_boxed_4605_ = lean_unbox(v_t_4602_);
v_res_4606_ = l_IO_Process_Stdio_ctorElim(v_motive_4600_, v_ctorIdx_4601_, v_t_boxed_4605_, v_h_4603_, v_k_4604_);
lean_dec(v_k_4604_);
lean_dec(v_ctorIdx_4601_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg(lean_object* v_piped_4607_){
_start:
{
lean_inc(v_piped_4607_);
return v_piped_4607_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg___boxed(lean_object* v_piped_4608_){
_start:
{
lean_object* v_res_4609_; 
v_res_4609_ = l_IO_Process_Stdio_piped_elim___redArg(v_piped_4608_);
lean_dec(v_piped_4608_);
return v_res_4609_;
}
}
lean_object* l_IO_Process_Stdio_piped_elim(lean_object* v_motive_4610_, uint8_t v_t_4611_, lean_object* v_h_4612_, lean_object* v_piped_4613_){
_start:
{
lean_inc(v_piped_4613_);
return v_piped_4613_;
}
}
LEAN_EXPORT void l_IO_Process_Stdio_piped_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_4611_ = stack[1].m_num;
lean_object* v_piped_4613_ = stack[3].m_obj;
lean_object* v_res_4614_;
v_res_4614_ = l_IO_Process_Stdio_piped_elim(lean_box(0), v_t_4611_, lean_box(0), v_piped_4613_);
stack->m_obj
 = v_res_4614_;
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___boxed(lean_object* v_motive_4615_, lean_object* v_t_4616_, lean_object* v_h_4617_, lean_object* v_piped_4618_){
_start:
{
uint8_t v_t_boxed_4619_; lean_object* v_res_4620_; 
v_t_boxed_4619_ = lean_unbox(v_t_4616_);
v_res_4620_ = l_IO_Process_Stdio_piped_elim(v_motive_4615_, v_t_boxed_4619_, v_h_4617_, v_piped_4618_);
lean_dec(v_piped_4618_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg(lean_object* v_inherit_4621_){
_start:
{
lean_inc(v_inherit_4621_);
return v_inherit_4621_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg___boxed(lean_object* v_inherit_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l_IO_Process_Stdio_inherit_elim___redArg(v_inherit_4622_);
lean_dec(v_inherit_4622_);
return v_res_4623_;
}
}
lean_object* l_IO_Process_Stdio_inherit_elim(lean_object* v_motive_4624_, uint8_t v_t_4625_, lean_object* v_h_4626_, lean_object* v_inherit_4627_){
_start:
{
lean_inc(v_inherit_4627_);
return v_inherit_4627_;
}
}
LEAN_EXPORT void l_IO_Process_Stdio_inherit_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_4625_ = stack[1].m_num;
lean_object* v_inherit_4627_ = stack[3].m_obj;
lean_object* v_res_4628_;
v_res_4628_ = l_IO_Process_Stdio_inherit_elim(lean_box(0), v_t_4625_, lean_box(0), v_inherit_4627_);
stack->m_obj
 = v_res_4628_;
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___boxed(lean_object* v_motive_4629_, lean_object* v_t_4630_, lean_object* v_h_4631_, lean_object* v_inherit_4632_){
_start:
{
uint8_t v_t_boxed_4633_; lean_object* v_res_4634_; 
v_t_boxed_4633_ = lean_unbox(v_t_4630_);
v_res_4634_ = l_IO_Process_Stdio_inherit_elim(v_motive_4629_, v_t_boxed_4633_, v_h_4631_, v_inherit_4632_);
lean_dec(v_inherit_4632_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg(lean_object* v_null_4635_){
_start:
{
lean_inc(v_null_4635_);
return v_null_4635_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg___boxed(lean_object* v_null_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l_IO_Process_Stdio_null_elim___redArg(v_null_4636_);
lean_dec(v_null_4636_);
return v_res_4637_;
}
}
lean_object* l_IO_Process_Stdio_null_elim(lean_object* v_motive_4638_, uint8_t v_t_4639_, lean_object* v_h_4640_, lean_object* v_null_4641_){
_start:
{
lean_inc(v_null_4641_);
return v_null_4641_;
}
}
LEAN_EXPORT void l_IO_Process_Stdio_null_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_4639_ = stack[1].m_num;
lean_object* v_null_4641_ = stack[3].m_obj;
lean_object* v_res_4642_;
v_res_4642_ = l_IO_Process_Stdio_null_elim(lean_box(0), v_t_4639_, lean_box(0), v_null_4641_);
stack->m_obj
 = v_res_4642_;
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___boxed(lean_object* v_motive_4643_, lean_object* v_t_4644_, lean_object* v_h_4645_, lean_object* v_null_4646_){
_start:
{
uint8_t v_t_boxed_4647_; lean_object* v_res_4648_; 
v_t_boxed_4647_ = lean_unbox(v_t_4644_);
v_res_4648_ = l_IO_Process_Stdio_null_elim(v_motive_4643_, v_t_boxed_4647_, v_h_4645_, v_null_4646_);
lean_dec(v_null_4646_);
return v_res_4648_;
}
}
LEAN_EXPORT void l_IO_Process_spawn_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_4649_ = stack[0].m_obj;
lean_object* v_res_4651_;
v_res_4651_ = lean_io_process_spawn(v_args_4649_);
stack->m_obj
 = v_res_4651_;
}
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object* v_args_4652_, lean_object* v_a_00___x40___internal___hyg_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = lean_io_process_spawn(v_args_4652_);
return v_res_4654_;
}
}
LEAN_EXPORT void l_IO_Process_Child_wait_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_4655_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_4656_ = stack[1].m_obj;
lean_object* v_res_4658_;
v_res_4658_ = lean_io_process_child_wait(v_cfg_4655_, v_a_00___x40___internal___hyg_4656_);
stack->m_obj
 = v_res_4658_;
}
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object* v_cfg_4659_, lean_object* v_a_00___x40___internal___hyg_4660_, lean_object* v_a_00___x40___internal___hyg_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = lean_io_process_child_wait(v_cfg_4659_, v_a_00___x40___internal___hyg_4660_);
lean_dec_ref(v_a_00___x40___internal___hyg_4660_);
lean_dec_ref(v_cfg_4659_);
return v_res_4662_;
}
}
LEAN_EXPORT void l_IO_Process_Child_tryWait_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_4663_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_4664_ = stack[1].m_obj;
lean_object* v_res_4666_;
v_res_4666_ = lean_io_process_child_try_wait(v_cfg_4663_, v_a_00___x40___internal___hyg_4664_);
stack->m_obj
 = v_res_4666_;
}
LEAN_EXPORT lean_object* l_IO_Process_Child_tryWait___boxed(lean_object* v_cfg_4667_, lean_object* v_a_00___x40___internal___hyg_4668_, lean_object* v_a_00___x40___internal___hyg_4669_){
_start:
{
lean_object* v_res_4670_; 
v_res_4670_ = lean_io_process_child_try_wait(v_cfg_4667_, v_a_00___x40___internal___hyg_4668_);
lean_dec_ref(v_a_00___x40___internal___hyg_4668_);
lean_dec_ref(v_cfg_4667_);
return v_res_4670_;
}
}
LEAN_EXPORT void l_IO_Process_Child_kill_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_4671_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_4672_ = stack[1].m_obj;
lean_object* v_res_4674_;
v_res_4674_ = lean_io_process_child_kill(v_cfg_4671_, v_a_00___x40___internal___hyg_4672_);
stack->m_obj
 = v_res_4674_;
}
LEAN_EXPORT lean_object* l_IO_Process_Child_kill___boxed(lean_object* v_cfg_4675_, lean_object* v_a_00___x40___internal___hyg_4676_, lean_object* v_a_00___x40___internal___hyg_4677_){
_start:
{
lean_object* v_res_4678_; 
v_res_4678_ = lean_io_process_child_kill(v_cfg_4675_, v_a_00___x40___internal___hyg_4676_);
lean_dec_ref(v_a_00___x40___internal___hyg_4676_);
lean_dec_ref(v_cfg_4675_);
return v_res_4678_;
}
}
LEAN_EXPORT void l_IO_Process_Child_takeStdin_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_4679_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_4680_ = stack[1].m_obj;
lean_object* v_res_4682_;
v_res_4682_ = lean_io_process_child_take_stdin(v_cfg_4679_, v_a_00___x40___internal___hyg_4680_);
stack->m_obj
 = v_res_4682_;
}
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object* v_cfg_4683_, lean_object* v_a_00___x40___internal___hyg_4684_, lean_object* v_a_00___x40___internal___hyg_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = lean_io_process_child_take_stdin(v_cfg_4683_, v_a_00___x40___internal___hyg_4684_);
lean_dec_ref(v_cfg_4683_);
return v_res_4686_;
}
}
LEAN_EXPORT void l_IO_Process_Child_pid_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_4687_ = stack[0].m_obj;
lean_object* v_a_00___x40___internal___hyg_4688_ = stack[1].m_obj;
uint32_t v_res_4689_;
v_res_4689_ = lean_io_process_child_pid(v_cfg_4687_, v_a_00___x40___internal___hyg_4688_);
stack->m_num = v_res_4689_;
}
LEAN_EXPORT lean_object* l_IO_Process_Child_pid___boxed(lean_object* v_cfg_4690_, lean_object* v_a_00___x40___internal___hyg_4691_){
_start:
{
uint32_t v_res_4692_; lean_object* v_r_4693_; 
v_res_4692_ = lean_io_process_child_pid(v_cfg_4690_, v_a_00___x40___internal___hyg_4691_);
lean_dec_ref(v_cfg_4690_);
v_r_4693_ = lean_box_uint32(v_res_4692_);
return v_r_4693_;
}
}
lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(lean_object* v_e_4694_){
_start:
{
if (lean_obj_tag(v_e_4694_) == 0)
{
lean_object* v_a_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4705_; 
v_a_4696_ = lean_ctor_get(v_e_4694_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v_e_4694_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4698_ = v_e_4694_;
v_isShared_4699_ = v_isSharedCheck_4705_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_a_4696_);
lean_dec(v_e_4694_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4705_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4703_; 
v___x_4700_ = lean_io_error_to_string(v_a_4696_);
v___x_4701_ = lean_mk_io_user_error(v___x_4700_);
if (v_isShared_4699_ == 0)
{
lean_ctor_set_tag(v___x_4698_, 1);
lean_ctor_set(v___x_4698_, 0, v___x_4701_);
v___x_4703_ = v___x_4698_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v___x_4701_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
return v___x_4703_;
}
}
}
else
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4713_; 
v_a_4706_ = lean_ctor_get(v_e_4694_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v_e_4694_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4708_ = v_e_4694_;
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v_e_4694_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v___x_4711_; 
if (v_isShared_4709_ == 0)
{
lean_ctor_set_tag(v___x_4708_, 0);
v___x_4711_ = v___x_4708_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_a_4706_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4694_ = stack[0].m_obj;
lean_object* v_res_4714_;
v_res_4714_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_4694_);
stack->m_obj
 = v_res_4714_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg___boxed(lean_object* v_e_4715_, lean_object* v_a_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_4715_);
return v_res_4717_;
}
}
lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0(lean_object* v_00_u03b1_4718_, lean_object* v_e_4719_){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_4719_);
return v___x_4721_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00IO_Process_output_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4719_ = stack[1].m_obj;
lean_object* v_res_4722_;
v_res_4722_ = l_IO_ofExcept___at___00IO_Process_output_spec__0(lean_box(0), v_e_4719_);
stack->m_obj
 = v_res_4722_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___boxed(lean_object* v_00_u03b1_4723_, lean_object* v_e_4724_, lean_object* v_a_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l_IO_ofExcept___at___00IO_Process_output_spec__0(v_00_u03b1_4723_, v_e_4724_);
return v_res_4726_;
}
}
lean_object* l_IO_Process_output___lam__0(lean_object* v_stdout_4727_){
_start:
{
lean_object* v___x_4729_; 
v___x_4729_ = l_IO_FS_Handle_readToEnd(v_stdout_4727_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4737_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4732_ = v___x_4729_;
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4729_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4735_; 
if (v_isShared_4733_ == 0)
{
lean_ctor_set_tag(v___x_4732_, 1);
v___x_4735_ = v___x_4732_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
v_a_4738_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4740_ = v___x_4729_;
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4729_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
lean_ctor_set_tag(v___x_4740_, 0);
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
}
LEAN_EXPORT void l_IO_Process_output___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stdout_4727_ = stack[0].m_obj;
lean_object* v_res_4746_;
v_res_4746_ = l_IO_Process_output___lam__0(v_stdout_4727_);
stack->m_obj
 = v_res_4746_;
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0___boxed(lean_object* v_stdout_4747_, lean_object* v___y_4748_){
_start:
{
lean_object* v_res_4749_; 
v_res_4749_ = l_IO_Process_output___lam__0(v_stdout_4747_);
lean_dec(v_stdout_4747_);
return v_res_4749_;
}
}
lean_object* l_IO_Process_output(lean_object* v_args_4755_, lean_object* v_input_x3f_4756_){
_start:
{
lean_object* v_child_4759_; 
if (lean_obj_tag(v_input_x3f_4756_) == 1)
{
lean_object* v_val_4806_; lean_object* v___x_4807_; lean_object* v_cmd_4808_; lean_object* v_args_4809_; lean_object* v_cwd_4810_; lean_object* v_env_4811_; uint8_t v_inheritEnv_4812_; uint8_t v_setsid_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4860_; 
v_val_4806_ = lean_ctor_get(v_input_x3f_4756_, 0);
v___x_4807_ = ((lean_object*)(l_IO_Process_output___closed__1));
v_cmd_4808_ = lean_ctor_get(v_args_4755_, 1);
v_args_4809_ = lean_ctor_get(v_args_4755_, 2);
v_cwd_4810_ = lean_ctor_get(v_args_4755_, 3);
v_env_4811_ = lean_ctor_get(v_args_4755_, 4);
v_inheritEnv_4812_ = lean_ctor_get_uint8(v_args_4755_, sizeof(void*)*5);
v_setsid_4813_ = lean_ctor_get_uint8(v_args_4755_, sizeof(void*)*5 + 1);
v_isSharedCheck_4860_ = !lean_is_exclusive(v_args_4755_);
if (v_isSharedCheck_4860_ == 0)
{
lean_object* v_unused_4861_; 
v_unused_4861_ = lean_ctor_get(v_args_4755_, 0);
lean_dec(v_unused_4861_);
v___x_4815_ = v_args_4755_;
v_isShared_4816_ = v_isSharedCheck_4860_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_env_4811_);
lean_inc(v_cwd_4810_);
lean_inc(v_args_4809_);
lean_inc(v_cmd_4808_);
lean_dec(v_args_4755_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4860_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4818_; 
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 0, v___x_4807_);
v___x_4818_ = v___x_4815_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4807_);
lean_ctor_set(v_reuseFailAlloc_4859_, 1, v_cmd_4808_);
lean_ctor_set(v_reuseFailAlloc_4859_, 2, v_args_4809_);
lean_ctor_set(v_reuseFailAlloc_4859_, 3, v_cwd_4810_);
lean_ctor_set(v_reuseFailAlloc_4859_, 4, v_env_4811_);
lean_ctor_set_uint8(v_reuseFailAlloc_4859_, sizeof(void*)*5, v_inheritEnv_4812_);
lean_ctor_set_uint8(v_reuseFailAlloc_4859_, sizeof(void*)*5 + 1, v_setsid_4813_);
v___x_4818_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
lean_object* v___x_4819_; 
v___x_4819_ = lean_io_process_spawn(v___x_4818_);
if (lean_obj_tag(v___x_4819_) == 0)
{
lean_object* v_a_4820_; lean_object* v___x_4821_; 
v_a_4820_ = lean_ctor_get(v___x_4819_, 0);
lean_inc(v_a_4820_);
lean_dec_ref_known(v___x_4819_, 1);
v___x_4821_ = lean_io_process_child_take_stdin(v___x_4807_, v_a_4820_);
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_object* v_a_4822_; lean_object* v_fst_4823_; lean_object* v_snd_4824_; lean_object* v___x_4825_; 
v_a_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_a_4822_);
lean_dec_ref_known(v___x_4821_, 1);
v_fst_4823_ = lean_ctor_get(v_a_4822_, 0);
lean_inc(v_fst_4823_);
v_snd_4824_ = lean_ctor_get(v_a_4822_, 1);
lean_inc(v_snd_4824_);
lean_dec(v_a_4822_);
v___x_4825_ = lean_io_prim_handle_put_str(v_fst_4823_, v_val_4806_);
if (lean_obj_tag(v___x_4825_) == 0)
{
lean_object* v___x_4826_; 
lean_dec_ref_known(v___x_4825_, 1);
v___x_4826_ = lean_io_prim_handle_flush(v_fst_4823_);
lean_dec(v_fst_4823_);
if (lean_obj_tag(v___x_4826_) == 0)
{
lean_dec_ref_known(v___x_4826_, 1);
v_child_4759_ = v_snd_4824_;
goto v___jp_4758_;
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4834_; 
lean_dec(v_snd_4824_);
v_a_4827_ = lean_ctor_get(v___x_4826_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4826_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4829_ = v___x_4826_;
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4826_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v___x_4832_; 
if (v_isShared_4830_ == 0)
{
v___x_4832_ = v___x_4829_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4827_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
}
else
{
lean_object* v_a_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4842_; 
lean_dec(v_snd_4824_);
lean_dec(v_fst_4823_);
v_a_4835_ = lean_ctor_get(v___x_4825_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4825_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4837_ = v___x_4825_;
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_a_4835_);
lean_dec(v___x_4825_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4840_; 
if (v_isShared_4838_ == 0)
{
v___x_4840_ = v___x_4837_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4835_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
else
{
lean_object* v_a_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4850_; 
v_a_4843_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4850_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4850_ == 0)
{
v___x_4845_ = v___x_4821_;
v_isShared_4846_ = v_isSharedCheck_4850_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_a_4843_);
lean_dec(v___x_4821_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4850_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4848_; 
if (v_isShared_4846_ == 0)
{
v___x_4848_ = v___x_4845_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v_a_4843_);
v___x_4848_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
return v___x_4848_;
}
}
}
}
else
{
lean_object* v_a_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4858_; 
v_a_4851_ = lean_ctor_get(v___x_4819_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4853_ = v___x_4819_;
v_isShared_4854_ = v_isSharedCheck_4858_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_a_4851_);
lean_dec(v___x_4819_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4858_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4856_; 
if (v_isShared_4854_ == 0)
{
v___x_4856_ = v___x_4853_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v_a_4851_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
}
}
}
}
else
{
lean_object* v___x_4862_; lean_object* v_cmd_4863_; lean_object* v_args_4864_; lean_object* v_cwd_4865_; lean_object* v_env_4866_; uint8_t v_inheritEnv_4867_; uint8_t v_setsid_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4885_; 
v___x_4862_ = ((lean_object*)(l_IO_Process_output___closed__0));
v_cmd_4863_ = lean_ctor_get(v_args_4755_, 1);
v_args_4864_ = lean_ctor_get(v_args_4755_, 2);
v_cwd_4865_ = lean_ctor_get(v_args_4755_, 3);
v_env_4866_ = lean_ctor_get(v_args_4755_, 4);
v_inheritEnv_4867_ = lean_ctor_get_uint8(v_args_4755_, sizeof(void*)*5);
v_setsid_4868_ = lean_ctor_get_uint8(v_args_4755_, sizeof(void*)*5 + 1);
v_isSharedCheck_4885_ = !lean_is_exclusive(v_args_4755_);
if (v_isSharedCheck_4885_ == 0)
{
lean_object* v_unused_4886_; 
v_unused_4886_ = lean_ctor_get(v_args_4755_, 0);
lean_dec(v_unused_4886_);
v___x_4870_ = v_args_4755_;
v_isShared_4871_ = v_isSharedCheck_4885_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_env_4866_);
lean_inc(v_cwd_4865_);
lean_inc(v_args_4864_);
lean_inc(v_cmd_4863_);
lean_dec(v_args_4755_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4885_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4873_; 
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 0, v___x_4862_);
v___x_4873_ = v___x_4870_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4862_);
lean_ctor_set(v_reuseFailAlloc_4884_, 1, v_cmd_4863_);
lean_ctor_set(v_reuseFailAlloc_4884_, 2, v_args_4864_);
lean_ctor_set(v_reuseFailAlloc_4884_, 3, v_cwd_4865_);
lean_ctor_set(v_reuseFailAlloc_4884_, 4, v_env_4866_);
lean_ctor_set_uint8(v_reuseFailAlloc_4884_, sizeof(void*)*5, v_inheritEnv_4867_);
lean_ctor_set_uint8(v_reuseFailAlloc_4884_, sizeof(void*)*5 + 1, v_setsid_4868_);
v___x_4873_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
lean_object* v___x_4874_; 
v___x_4874_ = lean_io_process_spawn(v___x_4873_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v_a_4875_; 
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
lean_inc(v_a_4875_);
lean_dec_ref_known(v___x_4874_, 1);
v_child_4759_ = v_a_4875_;
goto v___jp_4758_;
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4883_; 
v_a_4876_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4878_ = v___x_4874_;
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4874_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4881_; 
if (v_isShared_4879_ == 0)
{
v___x_4881_ = v___x_4878_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_a_4876_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
}
}
v___jp_4758_:
{
lean_object* v_stdout_4760_; lean_object* v_stderr_4761_; lean_object* v___f_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
v_stdout_4760_ = lean_ctor_get(v_child_4759_, 1);
v_stderr_4761_ = lean_ctor_get(v_child_4759_, 2);
lean_inc(v_stdout_4760_);
v___f_4762_ = lean_alloc_closure((void*)(l_IO_Process_output___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4762_, 0, v_stdout_4760_);
v___x_4763_ = lean_unsigned_to_nat(9u);
v___x_4764_ = lean_io_as_task(v___f_4762_, v___x_4763_);
v___x_4765_ = l_IO_FS_Handle_readToEnd(v_stderr_4761_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; 
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
lean_inc(v_a_4766_);
lean_dec_ref_known(v___x_4765_, 1);
v___x_4767_ = ((lean_object*)(l_IO_Process_output___closed__0));
v___x_4768_ = lean_io_process_child_wait(v___x_4767_, v_child_4759_);
lean_dec_ref(v_child_4759_);
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_a_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v_a_4769_ = lean_ctor_get(v___x_4768_, 0);
lean_inc(v_a_4769_);
lean_dec_ref_known(v___x_4768_, 1);
v___x_4770_ = lean_task_get_own(v___x_4764_);
v___x_4771_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v___x_4770_);
if (lean_obj_tag(v___x_4771_) == 0)
{
lean_object* v_a_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4781_; 
v_a_4772_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4774_ = v___x_4771_;
v_isShared_4775_ = v_isSharedCheck_4781_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_a_4772_);
lean_dec(v___x_4771_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4781_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4776_; uint32_t v___x_4777_; lean_object* v___x_4779_; 
v___x_4776_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4776_, 0, v_a_4772_);
lean_ctor_set(v___x_4776_, 1, v_a_4766_);
v___x_4777_ = lean_unbox_uint32(v_a_4769_);
lean_dec(v_a_4769_);
lean_ctor_set_uint32(v___x_4776_, sizeof(void*)*2, v___x_4777_);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 0, v___x_4776_);
v___x_4779_ = v___x_4774_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4776_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
lean_dec(v_a_4769_);
lean_dec(v_a_4766_);
v_a_4782_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4771_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4771_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4797_; 
lean_dec(v_a_4766_);
lean_dec_ref(v___x_4764_);
v_a_4790_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4792_ = v___x_4768_;
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4768_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4790_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
lean_dec_ref(v___x_4764_);
lean_dec_ref(v_child_4759_);
v_a_4798_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4765_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4765_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
}
}
LEAN_EXPORT void l_IO_Process_output_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_4755_ = stack[0].m_obj;
lean_object* v_input_x3f_4756_ = stack[1].m_obj;
lean_object* v_res_4887_;
v_res_4887_ = l_IO_Process_output(v_args_4755_, v_input_x3f_4756_);
stack->m_obj
 = v_res_4887_;
}
LEAN_EXPORT lean_object* l_IO_Process_output___boxed(lean_object* v_args_4888_, lean_object* v_input_x3f_4889_, lean_object* v_a_4890_){
_start:
{
lean_object* v_res_4891_; 
v_res_4891_ = l_IO_Process_output(v_args_4888_, v_input_x3f_4889_);
lean_dec(v_input_x3f_4889_);
return v_res_4891_;
}
}
lean_object* l_IO_Process_run(lean_object* v_args_4895_, lean_object* v_input_x3f_4896_){
_start:
{
lean_object* v___x_4898_; 
lean_inc_ref(v_args_4895_);
v___x_4898_ = l_IO_Process_output(v_args_4895_, v_input_x3f_4896_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4926_; 
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4901_ = v___x_4898_;
v_isShared_4902_ = v_isSharedCheck_4926_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4898_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4926_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
uint32_t v_exitCode_4903_; lean_object* v_stdout_4904_; lean_object* v_stderr_4905_; uint32_t v___x_4906_; uint8_t v___x_4907_; 
v_exitCode_4903_ = lean_ctor_get_uint32(v_a_4899_, sizeof(void*)*2);
v_stdout_4904_ = lean_ctor_get(v_a_4899_, 0);
lean_inc_ref(v_stdout_4904_);
v_stderr_4905_ = lean_ctor_get(v_a_4899_, 1);
lean_inc_ref(v_stderr_4905_);
lean_dec(v_a_4899_);
v___x_4906_ = 0;
v___x_4907_ = lean_uint32_dec_eq(v_exitCode_4903_, v___x_4906_);
if (v___x_4907_ == 0)
{
lean_object* v_cmd_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4921_; 
lean_dec_ref(v_stdout_4904_);
v_cmd_4908_ = lean_ctor_get(v_args_4895_, 1);
lean_inc_ref(v_cmd_4908_);
lean_dec_ref(v_args_4895_);
v___x_4909_ = ((lean_object*)(l_IO_Process_run___closed__0));
v___x_4910_ = lean_string_append(v___x_4909_, v_cmd_4908_);
lean_dec_ref(v_cmd_4908_);
v___x_4911_ = ((lean_object*)(l_IO_Process_run___closed__1));
v___x_4912_ = lean_string_append(v___x_4910_, v___x_4911_);
v___x_4913_ = lean_uint32_to_nat(v_exitCode_4903_);
v___x_4914_ = l_Nat_reprFast(v___x_4913_);
v___x_4915_ = lean_string_append(v___x_4912_, v___x_4914_);
lean_dec_ref(v___x_4914_);
v___x_4916_ = ((lean_object*)(l_IO_Process_run___closed__2));
v___x_4917_ = lean_string_append(v___x_4915_, v___x_4916_);
v___x_4918_ = lean_string_append(v___x_4917_, v_stderr_4905_);
lean_dec_ref(v_stderr_4905_);
v___x_4919_ = lean_mk_io_user_error(v___x_4918_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set_tag(v___x_4901_, 1);
lean_ctor_set(v___x_4901_, 0, v___x_4919_);
v___x_4921_ = v___x_4901_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v___x_4919_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
else
{
lean_object* v___x_4924_; 
lean_dec_ref(v_stderr_4905_);
lean_dec_ref(v_args_4895_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 0, v_stdout_4904_);
v___x_4924_ = v___x_4901_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v_stdout_4904_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
}
}
else
{
lean_object* v_a_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4934_; 
lean_dec_ref(v_args_4895_);
v_a_4927_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4929_ = v___x_4898_;
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_a_4927_);
lean_dec(v___x_4898_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4932_; 
if (v_isShared_4930_ == 0)
{
v___x_4932_ = v___x_4929_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v_a_4927_);
v___x_4932_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
return v___x_4932_;
}
}
}
}
}
LEAN_EXPORT void l_IO_Process_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_4895_ = stack[0].m_obj;
lean_object* v_input_x3f_4896_ = stack[1].m_obj;
lean_object* v_res_4935_;
v_res_4935_ = l_IO_Process_run(v_args_4895_, v_input_x3f_4896_);
stack->m_obj
 = v_res_4935_;
}
LEAN_EXPORT lean_object* l_IO_Process_run___boxed(lean_object* v_args_4936_, lean_object* v_input_x3f_4937_, lean_object* v_a_4938_){
_start:
{
lean_object* v_res_4939_; 
v_res_4939_ = l_IO_Process_run(v_args_4936_, v_input_x3f_4937_);
lean_dec(v_input_x3f_4937_);
return v_res_4939_;
}
}
LEAN_EXPORT void l_IO_Process_exit_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_00___x40___internal___hyg_4941_ = stack[1].m_num;
lean_object* v_res_4943_;
v_res_4943_ = lean_io_exit(v_a_00___x40___internal___hyg_4941_);
stack->m_obj
 = v_res_4943_;
}
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object* v_00_u03b1_4944_, lean_object* v_a_00___x40___internal___hyg_4945_, lean_object* v_a_00___x40___internal___hyg_4946_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_4947_; lean_object* v_res_4948_; 
v_a_00___x40___internal___hyg_1__boxed_4947_ = lean_unbox(v_a_00___x40___internal___hyg_4945_);
v_res_4948_ = lean_io_exit(v_a_00___x40___internal___hyg_1__boxed_4947_);
return v_res_4948_;
}
}
LEAN_EXPORT void l_IO_Process_forceExit_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_00___x40___internal___hyg_4950_ = stack[1].m_num;
lean_object* v_res_4952_;
v_res_4952_ = lean_io_force_exit(v_a_00___x40___internal___hyg_4950_);
stack->m_obj
 = v_res_4952_;
}
LEAN_EXPORT lean_object* l_IO_Process_forceExit___boxed(lean_object* v_00_u03b1_4953_, lean_object* v_a_00___x40___internal___hyg_4954_, lean_object* v_a_00___x40___internal___hyg_4955_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_4956_; lean_object* v_res_4957_; 
v_a_00___x40___internal___hyg_1__boxed_4956_ = lean_unbox(v_a_00___x40___internal___hyg_4954_);
v_res_4957_ = lean_io_force_exit(v_a_00___x40___internal___hyg_1__boxed_4956_);
return v_res_4957_;
}
}
LEAN_EXPORT void l_IO_getTID_0interp(lean_interpreter_value* stack)
{
uint64_t v_res_4959_;
v_res_4959_ = lean_io_get_tid();
stack->m_num = v_res_4959_;
}
LEAN_EXPORT lean_object* l_IO_getTID___boxed(lean_object* v_a_00___x40___internal___hyg_4960_){
_start:
{
uint64_t v_res_4961_; lean_object* v_r_4962_; 
v_res_4961_ = lean_io_get_tid();
v_r_4962_ = lean_box_uint64(v_res_4961_);
return v_r_4962_;
}
}
uint32_t l_IO_AccessRight_flags(lean_object* v_acc_4963_){
_start:
{
uint32_t v___y_4965_; uint32_t v___y_4966_; uint32_t v___y_4967_; uint8_t v_read_4970_; uint8_t v_write_4971_; uint8_t v_execution_4972_; uint32_t v___y_4974_; uint32_t v___y_4975_; uint32_t v___y_4979_; 
v_read_4970_ = lean_ctor_get_uint8(v_acc_4963_, 0);
v_write_4971_ = lean_ctor_get_uint8(v_acc_4963_, 1);
v_execution_4972_ = lean_ctor_get_uint8(v_acc_4963_, 2);
if (v_read_4970_ == 0)
{
uint32_t v___x_4982_; 
v___x_4982_ = 0;
v___y_4979_ = v___x_4982_;
goto v___jp_4978_;
}
else
{
uint32_t v___x_4983_; 
v___x_4983_ = 4;
v___y_4979_ = v___x_4983_;
goto v___jp_4978_;
}
v___jp_4964_:
{
uint32_t v___x_4968_; uint32_t v___x_4969_; 
v___x_4968_ = lean_uint32_lor(v___y_4966_, v___y_4967_);
v___x_4969_ = lean_uint32_lor(v___y_4965_, v___x_4968_);
return v___x_4969_;
}
v___jp_4973_:
{
if (v_execution_4972_ == 0)
{
uint32_t v___x_4976_; 
v___x_4976_ = 0;
v___y_4965_ = v___y_4974_;
v___y_4966_ = v___y_4975_;
v___y_4967_ = v___x_4976_;
goto v___jp_4964_;
}
else
{
uint32_t v___x_4977_; 
v___x_4977_ = 1;
v___y_4965_ = v___y_4974_;
v___y_4966_ = v___y_4975_;
v___y_4967_ = v___x_4977_;
goto v___jp_4964_;
}
}
v___jp_4978_:
{
if (v_write_4971_ == 0)
{
uint32_t v___x_4980_; 
v___x_4980_ = 0;
v___y_4974_ = v___y_4979_;
v___y_4975_ = v___x_4980_;
goto v___jp_4973_;
}
else
{
uint32_t v___x_4981_; 
v___x_4981_ = 2;
v___y_4974_ = v___y_4979_;
v___y_4975_ = v___x_4981_;
goto v___jp_4973_;
}
}
}
}
LEAN_EXPORT void l_IO_AccessRight_flags_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_4963_ = stack[0].m_obj;
uint32_t v_res_4984_;
v_res_4984_ = l_IO_AccessRight_flags(v_acc_4963_);
stack->m_num = v_res_4984_;
}
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object* v_acc_4985_){
_start:
{
uint32_t v_res_4986_; lean_object* v_r_4987_; 
v_res_4986_ = l_IO_AccessRight_flags(v_acc_4985_);
lean_dec_ref(v_acc_4985_);
v_r_4987_ = lean_box_uint32(v_res_4986_);
return v_r_4987_;
}
}
uint32_t l_IO_FileRight_flags(lean_object* v_acc_4988_){
_start:
{
lean_object* v_user_4989_; lean_object* v_group_4990_; lean_object* v_other_4991_; uint32_t v___x_4992_; uint32_t v___x_4993_; uint32_t v_u_4994_; uint32_t v___x_4995_; uint32_t v___x_4996_; uint32_t v_g_4997_; uint32_t v_o_4998_; uint32_t v___x_4999_; uint32_t v___x_5000_; 
v_user_4989_ = lean_ctor_get(v_acc_4988_, 0);
v_group_4990_ = lean_ctor_get(v_acc_4988_, 1);
v_other_4991_ = lean_ctor_get(v_acc_4988_, 2);
v___x_4992_ = l_IO_AccessRight_flags(v_user_4989_);
v___x_4993_ = 6;
v_u_4994_ = lean_uint32_shift_left(v___x_4992_, v___x_4993_);
v___x_4995_ = l_IO_AccessRight_flags(v_group_4990_);
v___x_4996_ = 3;
v_g_4997_ = lean_uint32_shift_left(v___x_4995_, v___x_4996_);
v_o_4998_ = l_IO_AccessRight_flags(v_other_4991_);
v___x_4999_ = lean_uint32_lor(v_g_4997_, v_o_4998_);
v___x_5000_ = lean_uint32_lor(v_u_4994_, v___x_4999_);
return v___x_5000_;
}
}
LEAN_EXPORT void l_IO_FileRight_flags_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_4988_ = stack[0].m_obj;
uint32_t v_res_5001_;
v_res_5001_ = l_IO_FileRight_flags(v_acc_4988_);
stack->m_num = v_res_5001_;
}
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object* v_acc_5002_){
_start:
{
uint32_t v_res_5003_; lean_object* v_r_5004_; 
v_res_5003_ = l_IO_FileRight_flags(v_acc_5002_);
lean_dec_ref(v_acc_5002_);
v_r_5004_ = lean_box_uint32(v_res_5003_);
return v_r_5004_;
}
}
LEAN_EXPORT void l_IO_Prim_setAccessRights_0interp(lean_interpreter_value* stack)
{
lean_object* v_filename_5005_ = stack[0].m_obj;
uint32_t v_mode_5006_ = stack[1].m_num;
lean_object* v_res_5008_;
v_res_5008_ = lean_chmod(v_filename_5005_, v_mode_5006_);
stack->m_obj
 = v_res_5008_;
}
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object* v_filename_5009_, lean_object* v_mode_5010_, lean_object* v_a_00___x40___internal___hyg_5011_){
_start:
{
uint32_t v_mode_boxed_5012_; lean_object* v_res_5013_; 
v_mode_boxed_5012_ = lean_unbox_uint32(v_mode_5010_);
lean_dec(v_mode_5010_);
v_res_5013_ = lean_chmod(v_filename_5009_, v_mode_boxed_5012_);
lean_dec_ref(v_filename_5009_);
return v_res_5013_;
}
}
lean_object* l_IO_setAccessRights(lean_object* v_filename_5014_, lean_object* v_mode_5015_){
_start:
{
uint32_t v___x_5017_; lean_object* v___x_5018_; 
v___x_5017_ = l_IO_FileRight_flags(v_mode_5015_);
v___x_5018_ = lean_chmod(v_filename_5014_, v___x_5017_);
return v___x_5018_;
}
}
LEAN_EXPORT void l_IO_setAccessRights_0interp(lean_interpreter_value* stack)
{
lean_object* v_filename_5014_ = stack[0].m_obj;
lean_object* v_mode_5015_ = stack[1].m_obj;
lean_object* v_res_5019_;
v_res_5019_ = l_IO_setAccessRights(v_filename_5014_, v_mode_5015_);
stack->m_obj
 = v_res_5019_;
}
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object* v_filename_5020_, lean_object* v_mode_5021_, lean_object* v_a_5022_){
_start:
{
lean_object* v_res_5023_; 
v_res_5023_ = l_IO_setAccessRights(v_filename_5020_, v_mode_5021_);
lean_dec_ref(v_mode_5021_);
lean_dec_ref(v_filename_5020_);
return v_res_5023_;
}
}
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object* v_00_u03b1_5024_, lean_object* v_mx_5025_){
_start:
{
lean_object* v___x_5027_; 
v___x_5027_ = lean_apply_1(v_mx_5025_, lean_box(0));
return v___x_5027_;
}
}
LEAN_EXPORT void l_IO_instMonadLiftSTRealWorldBaseIO___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mx_5025_ = stack[1].m_obj;
lean_object* v_res_5028_;
v_res_5028_ = l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_box(0), v_mx_5025_);
stack->m_obj
 = v_res_5028_;
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object* v_00_u03b1_5029_, lean_object* v_mx_5030_, lean_object* v_s_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(v_00_u03b1_5029_, v_mx_5030_);
return v_res_5032_;
}
}
lean_object* l_IO_mkRef___redArg(lean_object* v_a_5035_){
_start:
{
lean_object* v___x_5037_; 
v___x_5037_ = lean_st_mk_ref(v_a_5035_);
return v___x_5037_;
}
}
LEAN_EXPORT void l_IO_mkRef___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5035_ = stack[0].m_obj;
lean_object* v_res_5038_;
v_res_5038_ = l_IO_mkRef___redArg(v_a_5035_);
stack->m_obj
 = v_res_5038_;
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg___boxed(lean_object* v_a_5039_, lean_object* v_a_5040_){
_start:
{
lean_object* v_res_5041_; 
v_res_5041_ = l_IO_mkRef___redArg(v_a_5039_);
return v_res_5041_;
}
}
lean_object* l_IO_mkRef(lean_object* v_00_u03b1_5042_, lean_object* v_a_5043_){
_start:
{
lean_object* v___x_5045_; 
v___x_5045_ = lean_st_mk_ref(v_a_5043_);
return v___x_5045_;
}
}
LEAN_EXPORT void l_IO_mkRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5043_ = stack[1].m_obj;
lean_object* v_res_5046_;
v_res_5046_ = l_IO_mkRef(lean_box(0), v_a_5043_);
stack->m_obj
 = v_res_5046_;
}
LEAN_EXPORT lean_object* l_IO_mkRef___boxed(lean_object* v_00_u03b1_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l_IO_mkRef(v_00_u03b1_5047_, v_a_5048_);
return v_res_5050_;
}
}
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object* v_h_5051_){
_start:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
lean_inc_n(v_h_5051_, 5);
v___x_5052_ = lean_alloc_closure((void*)(l_IO_FS_Handle_flush___boxed), 2, 1);
lean_closure_set(v___x_5052_, 0, v_h_5051_);
v___x_5053_ = lean_alloc_closure((void*)(l_IO_FS_Handle_read___boxed), 3, 1);
lean_closure_set(v___x_5053_, 0, v_h_5051_);
v___x_5054_ = lean_alloc_closure((void*)(l_IO_FS_Handle_write___boxed), 3, 1);
lean_closure_set(v___x_5054_, 0, v_h_5051_);
v___x_5055_ = lean_alloc_closure((void*)(l_IO_FS_Handle_getLine___boxed), 2, 1);
lean_closure_set(v___x_5055_, 0, v_h_5051_);
v___x_5056_ = lean_alloc_closure((void*)(l_IO_FS_Handle_putStr___boxed), 3, 1);
lean_closure_set(v___x_5056_, 0, v_h_5051_);
v___x_5057_ = lean_alloc_closure((void*)(l_IO_FS_Handle_isTty___boxed), 2, 1);
lean_closure_set(v___x_5057_, 0, v_h_5051_);
v___x_5058_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5058_, 0, v___x_5052_);
lean_ctor_set(v___x_5058_, 1, v___x_5053_);
lean_ctor_set(v___x_5058_, 2, v___x_5054_);
lean_ctor_set(v___x_5058_, 3, v___x_5055_);
lean_ctor_set(v___x_5058_, 4, v___x_5056_);
lean_ctor_set(v___x_5058_, 5, v___x_5057_);
return v___x_5058_;
}
}
lean_object* l_IO_FS_Stream_ofBuffer___lam__0(lean_object* v_r_5059_, size_t v_n_5060_){
_start:
{
lean_object* v___x_5062_; lean_object* v_data_5063_; lean_object* v_pos_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5078_; 
v___x_5062_ = lean_st_ref_take(v_r_5059_);
v_data_5063_ = lean_ctor_get(v___x_5062_, 0);
v_pos_5064_ = lean_ctor_get(v___x_5062_, 1);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5066_ = v___x_5062_;
v_isShared_5067_ = v_isSharedCheck_5078_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_pos_5064_);
lean_inc(v_data_5063_);
lean_dec(v___x_5062_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5078_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v_data_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5074_; 
v___x_5068_ = lean_usize_to_nat(v_n_5060_);
v___x_5069_ = lean_nat_add(v_pos_5064_, v___x_5068_);
lean_dec(v___x_5068_);
lean_inc(v_pos_5064_);
v_data_5070_ = l_ByteArray_extract(v_data_5063_, v_pos_5064_, v___x_5069_);
lean_dec(v___x_5069_);
v___x_5071_ = lean_byte_array_size(v_data_5070_);
v___x_5072_ = lean_nat_add(v_pos_5064_, v___x_5071_);
lean_dec(v_pos_5064_);
if (v_isShared_5067_ == 0)
{
lean_ctor_set(v___x_5066_, 1, v___x_5072_);
v___x_5074_ = v___x_5066_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_data_5063_);
lean_ctor_set(v_reuseFailAlloc_5077_, 1, v___x_5072_);
v___x_5074_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5075_ = lean_st_ref_put(v_r_5059_, v___x_5074_);
v___x_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5076_, 0, v_data_5070_);
return v___x_5076_;
}
}
}
}
LEAN_EXPORT void l_IO_FS_Stream_ofBuffer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_5059_ = stack[0].m_obj;
size_t v_n_5060_ = stack[1].m_num;
lean_object* v_res_5079_;
v_res_5079_ = l_IO_FS_Stream_ofBuffer___lam__0(v_r_5059_, v_n_5060_);
stack->m_obj
 = v_res_5079_;
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0___boxed(lean_object* v_r_5080_, lean_object* v_n_5081_, lean_object* v___y_5082_){
_start:
{
size_t v_n_boxed_5083_; lean_object* v_res_5084_; 
v_n_boxed_5083_ = lean_unbox_usize(v_n_5081_);
lean_dec(v_n_5081_);
v_res_5084_ = l_IO_FS_Stream_ofBuffer___lam__0(v_r_5080_, v_n_boxed_5083_);
lean_dec(v_r_5080_);
return v_res_5084_;
}
}
lean_object* l_IO_FS_Stream_ofBuffer___lam__1(lean_object* v_r_5085_, lean_object* v_data_5086_){
_start:
{
lean_object* v___x_5088_; lean_object* v_data_5089_; lean_object* v_pos_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5104_; 
v___x_5088_ = lean_st_ref_take(v_r_5085_);
v_data_5089_ = lean_ctor_get(v___x_5088_, 0);
v_pos_5090_ = lean_ctor_get(v___x_5088_, 1);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5088_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5092_ = v___x_5088_;
v_isShared_5093_ = v_isSharedCheck_5104_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_pos_5090_);
lean_inc(v_data_5089_);
lean_dec(v___x_5088_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5104_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5094_; lean_object* v___x_5095_; uint8_t v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5100_; 
v___x_5094_ = lean_unsigned_to_nat(0u);
v___x_5095_ = lean_byte_array_size(v_data_5086_);
v___x_5096_ = 0;
lean_inc(v_pos_5090_);
v___x_5097_ = lean_byte_array_copy_slice(v_data_5086_, v___x_5094_, v_data_5089_, v_pos_5090_, v___x_5095_, v___x_5096_);
v___x_5098_ = lean_nat_add(v_pos_5090_, v___x_5095_);
lean_dec(v_pos_5090_);
if (v_isShared_5093_ == 0)
{
lean_ctor_set(v___x_5092_, 1, v___x_5098_);
lean_ctor_set(v___x_5092_, 0, v___x_5097_);
v___x_5100_ = v___x_5092_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v___x_5097_);
lean_ctor_set(v_reuseFailAlloc_5103_, 1, v___x_5098_);
v___x_5100_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
lean_object* v___x_5101_; lean_object* v___x_5102_; 
v___x_5101_ = lean_st_ref_put(v_r_5085_, v___x_5100_);
v___x_5102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5102_, 0, v___x_5101_);
return v___x_5102_;
}
}
}
}
LEAN_EXPORT void l_IO_FS_Stream_ofBuffer___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_5085_ = stack[0].m_obj;
lean_object* v_data_5086_ = stack[1].m_obj;
lean_object* v_res_5105_;
v_res_5105_ = l_IO_FS_Stream_ofBuffer___lam__1(v_r_5085_, v_data_5086_);
stack->m_obj
 = v_res_5105_;
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1___boxed(lean_object* v_r_5106_, lean_object* v_data_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l_IO_FS_Stream_ofBuffer___lam__1(v_r_5106_, v_data_5107_);
lean_dec_ref(v_data_5107_);
lean_dec(v_r_5106_);
return v_res_5109_;
}
}
lean_object* l_IO_FS_Stream_ofBuffer___lam__2(lean_object* v_r_5110_, lean_object* v_s_5111_){
_start:
{
lean_object* v___x_5113_; lean_object* v_data_5114_; lean_object* v_pos_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5130_; 
v___x_5113_ = lean_st_ref_take(v_r_5110_);
v_data_5114_ = lean_ctor_get(v___x_5113_, 0);
v_pos_5115_ = lean_ctor_get(v___x_5113_, 1);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5117_ = v___x_5113_;
v_isShared_5118_ = v_isSharedCheck_5130_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_pos_5115_);
lean_inc(v_data_5114_);
lean_dec(v___x_5113_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5130_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v_data_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; uint8_t v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5126_; 
v_data_5119_ = lean_string_to_utf8(v_s_5111_);
v___x_5120_ = lean_unsigned_to_nat(0u);
v___x_5121_ = lean_byte_array_size(v_data_5119_);
v___x_5122_ = 0;
lean_inc(v_pos_5115_);
v___x_5123_ = lean_byte_array_copy_slice(v_data_5119_, v___x_5120_, v_data_5114_, v_pos_5115_, v___x_5121_, v___x_5122_);
lean_dec_ref(v_data_5119_);
v___x_5124_ = lean_nat_add(v_pos_5115_, v___x_5121_);
lean_dec(v_pos_5115_);
if (v_isShared_5118_ == 0)
{
lean_ctor_set(v___x_5117_, 1, v___x_5124_);
lean_ctor_set(v___x_5117_, 0, v___x_5123_);
v___x_5126_ = v___x_5117_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5123_);
lean_ctor_set(v_reuseFailAlloc_5129_, 1, v___x_5124_);
v___x_5126_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
lean_object* v___x_5127_; lean_object* v___x_5128_; 
v___x_5127_ = lean_st_ref_put(v_r_5110_, v___x_5126_);
v___x_5128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5128_, 0, v___x_5127_);
return v___x_5128_;
}
}
}
}
LEAN_EXPORT void l_IO_FS_Stream_ofBuffer___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_5110_ = stack[0].m_obj;
lean_object* v_s_5111_ = stack[1].m_obj;
lean_object* v_res_5131_;
v_res_5131_ = l_IO_FS_Stream_ofBuffer___lam__2(v_r_5110_, v_s_5111_);
stack->m_obj
 = v_res_5131_;
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2___boxed(lean_object* v_r_5132_, lean_object* v_s_5133_, lean_object* v___y_5134_){
_start:
{
lean_object* v_res_5135_; 
v_res_5135_ = l_IO_FS_Stream_ofBuffer___lam__2(v_r_5132_, v_s_5133_);
lean_dec_ref(v_s_5133_);
lean_dec(v_r_5132_);
return v_res_5135_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(lean_object* v_a_5136_, lean_object* v_i_5137_){
_start:
{
lean_object* v___x_5138_; uint8_t v___x_5139_; 
v___x_5138_ = lean_byte_array_size(v_a_5136_);
v___x_5139_ = lean_nat_dec_lt(v_i_5137_, v___x_5138_);
if (v___x_5139_ == 0)
{
lean_object* v___x_5140_; 
lean_dec(v_i_5137_);
v___x_5140_ = lean_box(0);
return v___x_5140_;
}
else
{
uint8_t v___x_5141_; uint8_t v___x_5142_; uint8_t v___x_5143_; 
v___x_5141_ = lean_byte_array_fget(v_a_5136_, v_i_5137_);
v___x_5142_ = 0;
v___x_5143_ = lean_uint8_dec_eq(v___x_5141_, v___x_5142_);
if (v___x_5143_ == 0)
{
uint8_t v___x_5144_; uint8_t v___x_5145_; 
v___x_5144_ = 10;
v___x_5145_ = lean_uint8_dec_eq(v___x_5141_, v___x_5144_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; lean_object* v___x_5147_; 
v___x_5146_ = lean_unsigned_to_nat(1u);
v___x_5147_ = lean_nat_add(v_i_5137_, v___x_5146_);
lean_dec(v_i_5137_);
v_i_5137_ = v___x_5147_;
goto _start;
}
else
{
lean_object* v___x_5149_; 
v___x_5149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5149_, 0, v_i_5137_);
return v___x_5149_;
}
}
else
{
lean_object* v___x_5150_; 
v___x_5150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5150_, 0, v_i_5137_);
return v___x_5150_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0___boxed(lean_object* v_a_5151_, lean_object* v_i_5152_){
_start:
{
lean_object* v_res_5153_; 
v_res_5153_ = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(v_a_5151_, v_i_5152_);
lean_dec_ref(v_a_5151_);
return v_res_5153_;
}
}
lean_object* l_IO_FS_Stream_ofBuffer___lam__3(lean_object* v_r_5157_){
_start:
{
lean_object* v___x_5159_; lean_object* v_data_5160_; lean_object* v_pos_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5185_; 
v___x_5159_ = lean_st_ref_take(v_r_5157_);
v_data_5160_ = lean_ctor_get(v___x_5159_, 0);
v_pos_5161_ = lean_ctor_get(v___x_5159_, 1);
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5185_ == 0)
{
v___x_5163_ = v___x_5159_;
v_isShared_5164_ = v_isSharedCheck_5185_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_pos_5161_);
lean_inc(v_data_5160_);
lean_dec(v___x_5159_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5185_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___y_5166_; lean_object* v___x_5177_; 
lean_inc(v_pos_5161_);
v___x_5177_ = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(v_data_5160_, v_pos_5161_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_object* v___x_5178_; 
v___x_5178_ = lean_byte_array_size(v_data_5160_);
v___y_5166_ = v___x_5178_;
goto v___jp_5165_;
}
else
{
lean_object* v_val_5179_; uint8_t v___x_5180_; uint8_t v___x_5181_; uint8_t v___x_5182_; 
v_val_5179_ = lean_ctor_get(v___x_5177_, 0);
lean_inc(v_val_5179_);
lean_dec_ref_known(v___x_5177_, 1);
v___x_5180_ = lean_byte_array_get(v_data_5160_, v_val_5179_);
v___x_5181_ = 0;
v___x_5182_ = lean_uint8_dec_eq(v___x_5180_, v___x_5181_);
if (v___x_5182_ == 0)
{
lean_object* v___x_5183_; lean_object* v___x_5184_; 
v___x_5183_ = lean_unsigned_to_nat(1u);
v___x_5184_ = lean_nat_add(v_val_5179_, v___x_5183_);
lean_dec(v_val_5179_);
v___y_5166_ = v___x_5184_;
goto v___jp_5165_;
}
else
{
v___y_5166_ = v_val_5179_;
goto v___jp_5165_;
}
}
v___jp_5165_:
{
lean_object* v___x_5167_; lean_object* v___x_5169_; 
v___x_5167_ = l_ByteArray_extract(v_data_5160_, v_pos_5161_, v___y_5166_);
if (v_isShared_5164_ == 0)
{
lean_ctor_set(v___x_5163_, 1, v___y_5166_);
v___x_5169_ = v___x_5163_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_data_5160_);
lean_ctor_set(v_reuseFailAlloc_5176_, 1, v___y_5166_);
v___x_5169_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
lean_object* v___x_5170_; uint8_t v___x_5171_; 
v___x_5170_ = lean_st_ref_put(v_r_5157_, v___x_5169_);
v___x_5171_ = lean_string_validate_utf8(v___x_5167_);
if (v___x_5171_ == 0)
{
lean_object* v___x_5172_; lean_object* v___x_5173_; 
lean_dec_ref(v___x_5167_);
v___x_5172_ = ((lean_object*)(l_IO_FS_Stream_ofBuffer___lam__3___closed__1));
v___x_5173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5173_, 0, v___x_5172_);
return v___x_5173_;
}
else
{
lean_object* v___x_5174_; lean_object* v___x_5175_; 
v___x_5174_ = lean_string_from_utf8_unchecked(v___x_5167_);
v___x_5175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5175_, 0, v___x_5174_);
return v___x_5175_;
}
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_Stream_ofBuffer___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_5157_ = stack[0].m_obj;
lean_object* v_res_5186_;
v_res_5186_ = l_IO_FS_Stream_ofBuffer___lam__3(v_r_5157_);
stack->m_obj
 = v_res_5186_;
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3___boxed(lean_object* v_r_5187_, lean_object* v___y_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l_IO_FS_Stream_ofBuffer___lam__3(v_r_5187_);
lean_dec(v_r_5187_);
return v_res_5189_;
}
}
lean_object* l_IO_FS_Stream_ofBuffer___lam__4(lean_object* v___x_5190_){
_start:
{
lean_object* v___x_5192_; 
v___x_5192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5190_);
return v___x_5192_;
}
}
LEAN_EXPORT void l_IO_FS_Stream_ofBuffer___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5190_ = stack[0].m_obj;
lean_object* v_res_5193_;
v_res_5193_ = l_IO_FS_Stream_ofBuffer___lam__4(v___x_5190_);
stack->m_obj
 = v_res_5193_;
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4___boxed(lean_object* v___x_5194_, lean_object* v___y_5195_){
_start:
{
lean_object* v_res_5196_; 
v_res_5196_ = l_IO_FS_Stream_ofBuffer___lam__4(v___x_5194_);
return v_res_5196_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object* v_r_5199_){
_start:
{
lean_object* v___f_5200_; lean_object* v___f_5201_; lean_object* v___f_5202_; lean_object* v___f_5203_; lean_object* v___f_5204_; lean_object* v___f_5205_; lean_object* v___x_5206_; 
lean_inc_n(v_r_5199_, 3);
v___f_5200_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5200_, 0, v_r_5199_);
v___f_5201_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__1___boxed), 3, 1);
lean_closure_set(v___f_5201_, 0, v_r_5199_);
v___f_5202_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5202_, 0, v_r_5199_);
v___f_5203_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__3___boxed), 2, 1);
lean_closure_set(v___f_5203_, 0, v_r_5199_);
v___f_5204_ = ((lean_object*)(l_IO_FS_Stream_ofBuffer___closed__0));
v___f_5205_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___closed__5));
v___x_5206_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5206_, 0, v___f_5204_);
lean_ctor_set(v___x_5206_, 1, v___f_5200_);
lean_ctor_set(v___x_5206_, 2, v___f_5201_);
lean_ctor_set(v___x_5206_, 3, v___f_5203_);
lean_ctor_set(v___x_5206_, 4, v___f_5202_);
lean_ctor_set(v___x_5206_, 5, v___f_5205_);
return v___x_5206_;
}
}
lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(lean_object* v_s_5209_, lean_object* v_acc_5210_){
_start:
{
lean_object* v_read_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; 
v_read_5212_ = lean_ctor_get(v_s_5209_, 1);
v___x_5213_ = ((lean_object*)(l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1));
lean_inc_ref(v_read_5212_);
v___x_5214_ = lean_apply_2(v_read_5212_, v___x_5213_, lean_box(0));
if (lean_obj_tag(v___x_5214_) == 0)
{
lean_object* v_a_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5228_; 
v_a_5215_ = lean_ctor_get(v___x_5214_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5214_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5217_ = v___x_5214_;
v_isShared_5218_ = v_isSharedCheck_5228_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_a_5215_);
lean_dec(v___x_5214_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5228_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
uint8_t v___x_5219_; 
v___x_5219_ = l_ByteArray_isEmpty(v_a_5215_);
if (v___x_5219_ == 0)
{
lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; 
lean_del_object(v___x_5217_);
v___x_5220_ = lean_unsigned_to_nat(0u);
v___x_5221_ = lean_byte_array_size(v_acc_5210_);
v___x_5222_ = lean_byte_array_size(v_a_5215_);
v___x_5223_ = lean_byte_array_copy_slice(v_a_5215_, v___x_5220_, v_acc_5210_, v___x_5221_, v___x_5222_, v___x_5219_);
lean_dec(v_a_5215_);
v_acc_5210_ = v___x_5223_;
goto _start;
}
else
{
lean_object* v___x_5226_; 
lean_dec(v_a_5215_);
lean_dec_ref(v_s_5209_);
if (v_isShared_5218_ == 0)
{
lean_ctor_set(v___x_5217_, 0, v_acc_5210_);
v___x_5226_ = v___x_5217_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_acc_5210_);
v___x_5226_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
return v___x_5226_;
}
}
}
}
else
{
lean_dec_ref(v_acc_5210_);
lean_dec_ref(v_s_5209_);
return v___x_5214_;
}
}
}
LEAN_EXPORT void l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_5209_ = stack[0].m_obj;
lean_object* v_acc_5210_ = stack[1].m_obj;
lean_object* v_res_5229_;
v_res_5229_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_5209_, v_acc_5210_);
stack->m_obj
 = v_res_5229_;
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed(lean_object* v_s_5230_, lean_object* v_acc_5231_, lean_object* v_a_5232_){
_start:
{
lean_object* v_res_5233_; 
v_res_5233_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_5230_, v_acc_5231_);
return v_res_5233_;
}
}
lean_object* l_IO_FS_Stream_readBinToEndInto(lean_object* v_s_5234_, lean_object* v_buf_5235_){
_start:
{
lean_object* v___x_5237_; 
v___x_5237_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_5234_, v_buf_5235_);
return v___x_5237_;
}
}
LEAN_EXPORT void l_IO_FS_Stream_readBinToEndInto_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_5234_ = stack[0].m_obj;
lean_object* v_buf_5235_ = stack[1].m_obj;
lean_object* v_res_5238_;
v_res_5238_ = l_IO_FS_Stream_readBinToEndInto(v_s_5234_, v_buf_5235_);
stack->m_obj
 = v_res_5238_;
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto___boxed(lean_object* v_s_5239_, lean_object* v_buf_5240_, lean_object* v_a_5241_){
_start:
{
lean_object* v_res_5242_; 
v_res_5242_ = l_IO_FS_Stream_readBinToEndInto(v_s_5239_, v_buf_5240_);
return v_res_5242_;
}
}
lean_object* l_IO_FS_Stream_readBinToEnd(lean_object* v_s_5243_){
_start:
{
lean_object* v___x_5245_; lean_object* v___x_5246_; 
v___x_5245_ = l_ByteArray_empty;
v___x_5246_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_5243_, v___x_5245_);
return v___x_5246_;
}
}
LEAN_EXPORT void l_IO_FS_Stream_readBinToEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_5243_ = stack[0].m_obj;
lean_object* v_res_5247_;
v_res_5247_ = l_IO_FS_Stream_readBinToEnd(v_s_5243_);
stack->m_obj
 = v_res_5247_;
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd___boxed(lean_object* v_s_5248_, lean_object* v_a_5249_){
_start:
{
lean_object* v_res_5250_; 
v_res_5250_ = l_IO_FS_Stream_readBinToEnd(v_s_5248_);
return v_res_5250_;
}
}
lean_object* l_IO_FS_Stream_readToEnd(lean_object* v_s_5254_){
_start:
{
lean_object* v___x_5256_; 
v___x_5256_ = l_IO_FS_Stream_readBinToEnd(v_s_5254_);
if (lean_obj_tag(v___x_5256_) == 0)
{
lean_object* v_a_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5270_; 
v_a_5257_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5270_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5270_ == 0)
{
v___x_5259_ = v___x_5256_;
v_isShared_5260_ = v_isSharedCheck_5270_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_a_5257_);
lean_dec(v___x_5256_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5270_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
uint8_t v___x_5261_; 
v___x_5261_ = lean_string_validate_utf8(v_a_5257_);
if (v___x_5261_ == 0)
{
lean_object* v___x_5262_; lean_object* v___x_5264_; 
lean_dec(v_a_5257_);
v___x_5262_ = ((lean_object*)(l_IO_FS_Stream_readToEnd___closed__1));
if (v_isShared_5260_ == 0)
{
lean_ctor_set_tag(v___x_5259_, 1);
lean_ctor_set(v___x_5259_, 0, v___x_5262_);
v___x_5264_ = v___x_5259_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v___x_5262_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
else
{
lean_object* v___x_5266_; lean_object* v___x_5268_; 
v___x_5266_ = lean_string_from_utf8_unchecked(v_a_5257_);
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 0, v___x_5266_);
v___x_5268_ = v___x_5259_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v___x_5266_);
v___x_5268_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
return v___x_5268_;
}
}
}
}
else
{
lean_object* v_a_5271_; lean_object* v___x_5273_; uint8_t v_isShared_5274_; uint8_t v_isSharedCheck_5278_; 
v_a_5271_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5278_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5278_ == 0)
{
v___x_5273_ = v___x_5256_;
v_isShared_5274_ = v_isSharedCheck_5278_;
goto v_resetjp_5272_;
}
else
{
lean_inc(v_a_5271_);
lean_dec(v___x_5256_);
v___x_5273_ = lean_box(0);
v_isShared_5274_ = v_isSharedCheck_5278_;
goto v_resetjp_5272_;
}
v_resetjp_5272_:
{
lean_object* v___x_5276_; 
if (v_isShared_5274_ == 0)
{
v___x_5276_ = v___x_5273_;
goto v_reusejp_5275_;
}
else
{
lean_object* v_reuseFailAlloc_5277_; 
v_reuseFailAlloc_5277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5277_, 0, v_a_5271_);
v___x_5276_ = v_reuseFailAlloc_5277_;
goto v_reusejp_5275_;
}
v_reusejp_5275_:
{
return v___x_5276_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_Stream_readToEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_5254_ = stack[0].m_obj;
lean_object* v_res_5279_;
v_res_5279_ = l_IO_FS_Stream_readToEnd(v_s_5254_);
stack->m_obj
 = v_res_5279_;
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd___boxed(lean_object* v_s_5280_, lean_object* v_a_5281_){
_start:
{
lean_object* v_res_5282_; 
v_res_5282_ = l_IO_FS_Stream_readToEnd(v_s_5280_);
return v_res_5282_;
}
}
lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read(lean_object* v_s_5283_, lean_object* v_lines_5284_){
_start:
{
lean_object* v_getLine_5286_; lean_object* v___x_5287_; 
v_getLine_5286_ = lean_ctor_get(v_s_5283_, 3);
lean_inc_ref(v_getLine_5286_);
v___x_5287_ = lean_apply_1(v_getLine_5286_, lean_box(0));
if (lean_obj_tag(v___x_5287_) == 0)
{
lean_object* v_a_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5345_; 
v_a_5288_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5345_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5345_ == 0)
{
v___x_5290_ = v___x_5287_;
v_isShared_5291_ = v_isSharedCheck_5345_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_dec(v___x_5287_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5345_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___y_5293_; lean_object* v___y_5297_; lean_object* v___y_5298_; lean_object* v___y_5299_; uint32_t v___y_5300_; lean_object* v___y_5308_; lean_object* v___y_5309_; lean_object* v___y_5310_; uint32_t v___y_5313_; lean_object* v___x_5335_; lean_object* v___x_5336_; uint8_t v___x_5337_; 
v___x_5335_ = lean_string_utf8_byte_size(v_a_5288_);
v___x_5336_ = lean_unsigned_to_nat(0u);
v___x_5337_ = lean_nat_dec_eq(v___x_5335_, v___x_5336_);
if (v___x_5337_ == 0)
{
lean_object* v___x_5338_; lean_object* v___x_5339_; 
lean_inc(v_a_5288_);
v___x_5338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5338_, 0, v_a_5288_);
lean_ctor_set(v___x_5338_, 1, v___x_5336_);
lean_ctor_set(v___x_5338_, 2, v___x_5335_);
v___x_5339_ = l_String_Slice_Pos_prev_x3f(v___x_5338_, v___x_5335_);
if (lean_obj_tag(v___x_5339_) == 0)
{
lean_dec_ref_known(v___x_5338_, 3);
goto v___jp_5333_;
}
else
{
lean_object* v_val_5340_; lean_object* v___x_5341_; 
v_val_5340_ = lean_ctor_get(v___x_5339_, 0);
lean_inc(v_val_5340_);
lean_dec_ref_known(v___x_5339_, 1);
v___x_5341_ = l_String_Slice_Pos_get_x3f(v___x_5338_, v_val_5340_);
lean_dec(v_val_5340_);
lean_dec_ref_known(v___x_5338_, 3);
if (lean_obj_tag(v___x_5341_) == 0)
{
goto v___jp_5333_;
}
else
{
lean_object* v_val_5342_; uint32_t v___x_5343_; 
v_val_5342_ = lean_ctor_get(v___x_5341_, 0);
lean_inc(v_val_5342_);
lean_dec_ref_known(v___x_5341_, 1);
v___x_5343_ = lean_unbox_uint32(v_val_5342_);
lean_dec(v_val_5342_);
v___y_5313_ = v___x_5343_;
goto v___jp_5312_;
}
}
}
else
{
lean_object* v___x_5344_; 
lean_del_object(v___x_5290_);
lean_dec(v_a_5288_);
lean_dec_ref(v_s_5283_);
v___x_5344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5344_, 0, v_lines_5284_);
return v___x_5344_;
}
v___jp_5292_:
{
lean_object* v___x_5294_; 
v___x_5294_ = lean_array_push(v_lines_5284_, v___y_5293_);
v_lines_5284_ = v___x_5294_;
goto _start;
}
v___jp_5296_:
{
uint32_t v___x_5301_; uint8_t v___x_5302_; 
v___x_5301_ = 13;
v___x_5302_ = lean_uint32_dec_eq(v___y_5300_, v___x_5301_);
if (v___x_5302_ == 0)
{
lean_dec(v___y_5299_);
lean_dec(v___y_5297_);
v___y_5293_ = v___y_5298_;
goto v___jp_5292_;
}
else
{
lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; 
v___x_5303_ = lean_string_utf8_byte_size(v___y_5298_);
lean_inc(v___y_5297_);
lean_inc_ref(v___y_5298_);
v___x_5304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5304_, 0, v___y_5298_);
lean_ctor_set(v___x_5304_, 1, v___y_5297_);
lean_ctor_set(v___x_5304_, 2, v___x_5303_);
v___x_5305_ = l_String_Slice_Pos_prevn(v___x_5304_, v___x_5303_, v___y_5299_);
lean_dec_ref_known(v___x_5304_, 3);
v___x_5306_ = lean_string_utf8_extract_fast(v___y_5298_, v___y_5297_, v___x_5305_);
lean_dec(v___x_5305_);
lean_dec(v___y_5297_);
lean_dec_ref(v___y_5298_);
v___y_5293_ = v___x_5306_;
goto v___jp_5292_;
}
}
v___jp_5307_:
{
uint32_t v___x_5311_; 
v___x_5311_ = 65;
v___y_5297_ = v___y_5308_;
v___y_5298_ = v___y_5309_;
v___y_5299_ = v___y_5310_;
v___y_5300_ = v___x_5311_;
goto v___jp_5296_;
}
v___jp_5312_:
{
uint32_t v___x_5314_; uint8_t v___x_5315_; 
v___x_5314_ = 10;
v___x_5315_ = lean_uint32_dec_eq(v___y_5313_, v___x_5314_);
if (v___x_5315_ == 0)
{
lean_object* v___x_5316_; lean_object* v___x_5318_; 
lean_dec_ref(v_s_5283_);
v___x_5316_ = lean_array_push(v_lines_5284_, v_a_5288_);
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 0, v___x_5316_);
v___x_5318_ = v___x_5290_;
goto v_reusejp_5317_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v___x_5316_);
v___x_5318_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5317_;
}
v_reusejp_5317_:
{
return v___x_5318_;
}
}
else
{
lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; 
lean_del_object(v___x_5290_);
v___x_5320_ = lean_unsigned_to_nat(1u);
v___x_5321_ = lean_unsigned_to_nat(0u);
v___x_5322_ = lean_string_utf8_byte_size(v_a_5288_);
lean_inc(v_a_5288_);
v___x_5323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5323_, 0, v_a_5288_);
lean_ctor_set(v___x_5323_, 1, v___x_5321_);
lean_ctor_set(v___x_5323_, 2, v___x_5322_);
v___x_5324_ = l_String_Slice_Pos_prevn(v___x_5323_, v___x_5322_, v___x_5320_);
lean_dec_ref_known(v___x_5323_, 3);
v___x_5325_ = lean_string_utf8_extract_fast(v_a_5288_, v___x_5321_, v___x_5324_);
lean_dec(v___x_5324_);
lean_dec(v_a_5288_);
v___x_5326_ = lean_string_utf8_byte_size(v___x_5325_);
lean_inc_ref(v___x_5325_);
v___x_5327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5327_, 0, v___x_5325_);
lean_ctor_set(v___x_5327_, 1, v___x_5321_);
lean_ctor_set(v___x_5327_, 2, v___x_5326_);
v___x_5328_ = l_String_Slice_Pos_prev_x3f(v___x_5327_, v___x_5326_);
if (lean_obj_tag(v___x_5328_) == 0)
{
lean_dec_ref_known(v___x_5327_, 3);
v___y_5308_ = v___x_5321_;
v___y_5309_ = v___x_5325_;
v___y_5310_ = v___x_5320_;
goto v___jp_5307_;
}
else
{
lean_object* v_val_5329_; lean_object* v___x_5330_; 
v_val_5329_ = lean_ctor_get(v___x_5328_, 0);
lean_inc(v_val_5329_);
lean_dec_ref_known(v___x_5328_, 1);
v___x_5330_ = l_String_Slice_Pos_get_x3f(v___x_5327_, v_val_5329_);
lean_dec(v_val_5329_);
lean_dec_ref_known(v___x_5327_, 3);
if (lean_obj_tag(v___x_5330_) == 0)
{
v___y_5308_ = v___x_5321_;
v___y_5309_ = v___x_5325_;
v___y_5310_ = v___x_5320_;
goto v___jp_5307_;
}
else
{
lean_object* v_val_5331_; uint32_t v___x_5332_; 
v_val_5331_ = lean_ctor_get(v___x_5330_, 0);
lean_inc(v_val_5331_);
lean_dec_ref_known(v___x_5330_, 1);
v___x_5332_ = lean_unbox_uint32(v_val_5331_);
lean_dec(v_val_5331_);
v___y_5297_ = v___x_5321_;
v___y_5298_ = v___x_5325_;
v___y_5299_ = v___x_5320_;
v___y_5300_ = v___x_5332_;
goto v___jp_5296_;
}
}
}
}
v___jp_5333_:
{
uint32_t v___x_5334_; 
v___x_5334_ = 65;
v___y_5313_ = v___x_5334_;
goto v___jp_5312_;
}
}
}
else
{
lean_object* v_a_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5353_; 
lean_dec_ref(v_lines_5284_);
lean_dec_ref(v_s_5283_);
v_a_5346_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5348_ = v___x_5287_;
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
else
{
lean_inc(v_a_5346_);
lean_dec(v___x_5287_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v___x_5351_; 
if (v_isShared_5349_ == 0)
{
v___x_5351_ = v___x_5348_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_a_5346_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_System_IO_0__IO_FS_Stream_lines_read_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_5283_ = stack[0].m_obj;
lean_object* v_lines_5284_ = stack[1].m_obj;
lean_object* v_res_5354_;
v_res_5354_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_5283_, v_lines_5284_);
stack->m_obj
 = v_res_5354_;
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read___boxed(lean_object* v_s_5355_, lean_object* v_lines_5356_, lean_object* v_a_5357_){
_start:
{
lean_object* v_res_5358_; 
v_res_5358_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_5355_, v_lines_5356_);
return v_res_5358_;
}
}
lean_object* l_IO_FS_Stream_lines(lean_object* v_s_5359_){
_start:
{
lean_object* v___x_5361_; lean_object* v___x_5362_; 
v___x_5361_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_5362_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_5359_, v___x_5361_);
return v___x_5362_;
}
}
LEAN_EXPORT void l_IO_FS_Stream_lines_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_5359_ = stack[0].m_obj;
lean_object* v_res_5363_;
v_res_5363_ = l_IO_FS_Stream_lines(v_s_5359_);
stack->m_obj
 = v_res_5363_;
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines___boxed(lean_object* v_s_5364_, lean_object* v_a_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l_IO_FS_Stream_lines(v_s_5364_);
return v_res_5366_;
}
}
lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0(lean_object* v_bOut_5367_){
_start:
{
lean_object* v___x_5369_; 
v___x_5369_ = lean_st_ref_get(v_bOut_5367_);
return v___x_5369_;
}
}
LEAN_EXPORT void l_IO_FS_withIsolatedStreams___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_bOut_5367_ = stack[0].m_obj;
lean_object* v_res_5370_;
v_res_5370_ = l_IO_FS_withIsolatedStreams___redArg___lam__0(v_bOut_5367_);
stack->m_obj
 = v_res_5370_;
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed(lean_object* v_bOut_5371_, lean_object* v___y_5372_){
_start:
{
lean_object* v_res_5373_; 
v_res_5373_ = l_IO_FS_withIsolatedStreams___redArg___lam__0(v_bOut_5371_);
lean_dec(v_bOut_5371_);
return v_res_5373_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; 
v___x_5378_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3));
v___x_5379_ = lean_unsigned_to_nat(46u);
v___x_5380_ = lean_unsigned_to_nat(193u);
v___x_5381_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2));
v___x_5382_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1));
v___x_5383_ = l_mkPanicMessageWithDecl(v___x_5382_, v___x_5381_, v___x_5380_, v___x_5379_, v___x_5378_);
return v___x_5383_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1(lean_object* v_r_5384_, lean_object* v_toPure_5385_, lean_object* v_bOut_5386_){
_start:
{
lean_object* v___y_5388_; lean_object* v_data_5391_; uint8_t v___x_5392_; 
v_data_5391_ = lean_ctor_get(v_bOut_5386_, 0);
lean_inc_ref(v_data_5391_);
lean_dec_ref(v_bOut_5386_);
v___x_5392_ = lean_string_validate_utf8(v_data_5391_);
if (v___x_5392_ == 0)
{
lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; 
lean_dec_ref(v_data_5391_);
v___x_5393_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0));
v___x_5394_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4, &l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4_once, _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4);
v___x_5395_ = l_panic___redArg(v___x_5393_, v___x_5394_);
v___y_5388_ = v___x_5395_;
goto v___jp_5387_;
}
else
{
lean_object* v___x_5396_; 
v___x_5396_ = lean_string_from_utf8_unchecked(v_data_5391_);
v___y_5388_ = v___x_5396_;
goto v___jp_5387_;
}
v___jp_5387_:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; 
v___x_5389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5389_, 0, v___y_5388_);
lean_ctor_set(v___x_5389_, 1, v_r_5384_);
v___x_5390_ = lean_apply_2(v_toPure_5385_, lean_box(0), v___x_5389_);
return v___x_5390_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__2(lean_object* v_toPure_5397_, lean_object* v_inst_5398_, lean_object* v___f_5399_, lean_object* v_toBind_5400_, lean_object* v_r_5401_){
_start:
{
lean_object* v___f_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___f_5402_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5402_, 0, v_r_5401_);
lean_closure_set(v___f_5402_, 1, v_toPure_5397_);
v___x_5403_ = lean_apply_2(v_inst_5398_, lean_box(0), v___f_5399_);
v___x_5404_ = lean_apply_4(v_toBind_5400_, lean_box(0), lean_box(0), v___x_5403_, v___f_5402_);
return v___x_5404_;
}
}
lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3(lean_object* v_toPure_5405_, lean_object* v_inst_5406_, lean_object* v_toBind_5407_, lean_object* v_bIn_5408_, lean_object* v_inst_5409_, lean_object* v_inst_5410_, uint8_t v_isolateStderr_5411_, lean_object* v_x_5412_, lean_object* v_bOut_5413_){
_start:
{
lean_object* v___f_5414_; lean_object* v___f_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___y_5419_; 
lean_inc(v_bOut_5413_);
v___f_5414_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5414_, 0, v_bOut_5413_);
lean_inc(v_toBind_5407_);
lean_inc(v_inst_5406_);
v___f_5415_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__2), 5, 4);
lean_closure_set(v___f_5415_, 0, v_toPure_5405_);
lean_closure_set(v___f_5415_, 1, v_inst_5406_);
lean_closure_set(v___f_5415_, 2, v___f_5414_);
lean_closure_set(v___f_5415_, 3, v_toBind_5407_);
v___x_5416_ = l_IO_FS_Stream_ofBuffer(v_bIn_5408_);
v___x_5417_ = l_IO_FS_Stream_ofBuffer(v_bOut_5413_);
if (v_isolateStderr_5411_ == 0)
{
v___y_5419_ = v_x_5412_;
goto v___jp_5418_;
}
else
{
lean_object* v___x_5423_; 
lean_inc_ref(v___x_5417_);
lean_inc(v_inst_5406_);
lean_inc(v_inst_5410_);
lean_inc_ref(v_inst_5409_);
v___x_5423_ = l_IO_withStderr___redArg(v_inst_5409_, v_inst_5410_, v_inst_5406_, v___x_5417_, v_x_5412_);
v___y_5419_ = v___x_5423_;
goto v___jp_5418_;
}
v___jp_5418_:
{
lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; 
lean_inc(v_inst_5406_);
lean_inc(v_inst_5410_);
lean_inc_ref(v_inst_5409_);
v___x_5420_ = l_IO_withStdout___redArg(v_inst_5409_, v_inst_5410_, v_inst_5406_, v___x_5417_, v___y_5419_);
v___x_5421_ = l_IO_withStdin___redArg(v_inst_5409_, v_inst_5410_, v_inst_5406_, v___x_5416_, v___x_5420_);
v___x_5422_ = lean_apply_4(v_toBind_5407_, lean_box(0), lean_box(0), v___x_5421_, v___f_5415_);
return v___x_5422_;
}
}
}
LEAN_EXPORT void l_IO_FS_withIsolatedStreams___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_5405_ = stack[0].m_obj;
lean_object* v_inst_5406_ = stack[1].m_obj;
lean_object* v_toBind_5407_ = stack[2].m_obj;
lean_object* v_bIn_5408_ = stack[3].m_obj;
lean_object* v_inst_5409_ = stack[4].m_obj;
lean_object* v_inst_5410_ = stack[5].m_obj;
uint8_t v_isolateStderr_5411_ = stack[6].m_num;
lean_object* v_x_5412_ = stack[7].m_obj;
lean_object* v_bOut_5413_ = stack[8].m_obj;
lean_object* v_res_5424_;
v_res_5424_ = l_IO_FS_withIsolatedStreams___redArg___lam__3(v_toPure_5405_, v_inst_5406_, v_toBind_5407_, v_bIn_5408_, v_inst_5409_, v_inst_5410_, v_isolateStderr_5411_, v_x_5412_, v_bOut_5413_);
stack->m_obj
 = v_res_5424_;
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed(lean_object* v_toPure_5425_, lean_object* v_inst_5426_, lean_object* v_toBind_5427_, lean_object* v_bIn_5428_, lean_object* v_inst_5429_, lean_object* v_inst_5430_, lean_object* v_isolateStderr_5431_, lean_object* v_x_5432_, lean_object* v_bOut_5433_){
_start:
{
uint8_t v_isolateStderr_boxed_5434_; lean_object* v_res_5435_; 
v_isolateStderr_boxed_5434_ = lean_unbox(v_isolateStderr_5431_);
v_res_5435_ = l_IO_FS_withIsolatedStreams___redArg___lam__3(v_toPure_5425_, v_inst_5426_, v_toBind_5427_, v_bIn_5428_, v_inst_5429_, v_inst_5430_, v_isolateStderr_boxed_5434_, v_x_5432_, v_bOut_5433_);
return v_res_5435_;
}
}
lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4(lean_object* v_toPure_5436_, lean_object* v_inst_5437_, lean_object* v_toBind_5438_, lean_object* v_inst_5439_, lean_object* v_inst_5440_, uint8_t v_isolateStderr_5441_, lean_object* v_x_5442_, lean_object* v___x_5443_, lean_object* v_bIn_5444_){
_start:
{
lean_object* v___x_5445_; lean_object* v___f_5446_; lean_object* v___x_5447_; 
v___x_5445_ = lean_box(v_isolateStderr_5441_);
lean_inc(v_toBind_5438_);
v___f_5446_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_5446_, 0, v_toPure_5436_);
lean_closure_set(v___f_5446_, 1, v_inst_5437_);
lean_closure_set(v___f_5446_, 2, v_toBind_5438_);
lean_closure_set(v___f_5446_, 3, v_bIn_5444_);
lean_closure_set(v___f_5446_, 4, v_inst_5439_);
lean_closure_set(v___f_5446_, 5, v_inst_5440_);
lean_closure_set(v___f_5446_, 6, v___x_5445_);
lean_closure_set(v___f_5446_, 7, v_x_5442_);
v___x_5447_ = lean_apply_4(v_toBind_5438_, lean_box(0), lean_box(0), v___x_5443_, v___f_5446_);
return v___x_5447_;
}
}
LEAN_EXPORT void l_IO_FS_withIsolatedStreams___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_5436_ = stack[0].m_obj;
lean_object* v_inst_5437_ = stack[1].m_obj;
lean_object* v_toBind_5438_ = stack[2].m_obj;
lean_object* v_inst_5439_ = stack[3].m_obj;
lean_object* v_inst_5440_ = stack[4].m_obj;
uint8_t v_isolateStderr_5441_ = stack[5].m_num;
lean_object* v_x_5442_ = stack[6].m_obj;
lean_object* v___x_5443_ = stack[7].m_obj;
lean_object* v_bIn_5444_ = stack[8].m_obj;
lean_object* v_res_5448_;
v_res_5448_ = l_IO_FS_withIsolatedStreams___redArg___lam__4(v_toPure_5436_, v_inst_5437_, v_toBind_5438_, v_inst_5439_, v_inst_5440_, v_isolateStderr_5441_, v_x_5442_, v___x_5443_, v_bIn_5444_);
stack->m_obj
 = v_res_5448_;
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed(lean_object* v_toPure_5449_, lean_object* v_inst_5450_, lean_object* v_toBind_5451_, lean_object* v_inst_5452_, lean_object* v_inst_5453_, lean_object* v_isolateStderr_5454_, lean_object* v_x_5455_, lean_object* v___x_5456_, lean_object* v_bIn_5457_){
_start:
{
uint8_t v_isolateStderr_boxed_5458_; lean_object* v_res_5459_; 
v_isolateStderr_boxed_5458_ = lean_unbox(v_isolateStderr_5454_);
v_res_5459_ = l_IO_FS_withIsolatedStreams___redArg___lam__4(v_toPure_5449_, v_inst_5450_, v_toBind_5451_, v_inst_5452_, v_inst_5453_, v_isolateStderr_boxed_5458_, v_x_5455_, v___x_5456_, v_bIn_5457_);
return v_res_5459_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__0(void){
_start:
{
lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; 
v___x_5460_ = lean_unsigned_to_nat(0u);
v___x_5461_ = l_ByteArray_empty;
v___x_5462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5462_, 0, v___x_5461_);
lean_ctor_set(v___x_5462_, 1, v___x_5460_);
return v___x_5462_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__1(void){
_start:
{
lean_object* v___x_5463_; lean_object* v___x_5464_; 
v___x_5463_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___closed__0, &l_IO_FS_withIsolatedStreams___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___redArg___closed__0);
v___x_5464_ = lean_alloc_closure((void*)(l_IO_mkRef___boxed), 3, 2);
lean_closure_set(v___x_5464_, 0, lean_box(0));
lean_closure_set(v___x_5464_, 1, v___x_5463_);
return v___x_5464_;
}
}
lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object* v_inst_5465_, lean_object* v_inst_5466_, lean_object* v_inst_5467_, lean_object* v_x_5468_, uint8_t v_isolateStderr_5469_){
_start:
{
lean_object* v_toApplicative_5470_; lean_object* v_toBind_5471_; lean_object* v_toPure_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___f_5476_; lean_object* v___x_5477_; 
v_toApplicative_5470_ = lean_ctor_get(v_inst_5465_, 0);
v_toBind_5471_ = lean_ctor_get(v_inst_5465_, 1);
lean_inc_n(v_toBind_5471_, 2);
v_toPure_5472_ = lean_ctor_get(v_toApplicative_5470_, 1);
lean_inc(v_toPure_5472_);
v___x_5473_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___closed__1, &l_IO_FS_withIsolatedStreams___redArg___closed__1_once, _init_l_IO_FS_withIsolatedStreams___redArg___closed__1);
lean_inc(v_inst_5467_);
v___x_5474_ = lean_apply_2(v_inst_5467_, lean_box(0), v___x_5473_);
v___x_5475_ = lean_box(v_isolateStderr_5469_);
lean_inc(v___x_5474_);
v___f_5476_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_5476_, 0, v_toPure_5472_);
lean_closure_set(v___f_5476_, 1, v_inst_5467_);
lean_closure_set(v___f_5476_, 2, v_toBind_5471_);
lean_closure_set(v___f_5476_, 3, v_inst_5465_);
lean_closure_set(v___f_5476_, 4, v_inst_5466_);
lean_closure_set(v___f_5476_, 5, v___x_5475_);
lean_closure_set(v___f_5476_, 6, v_x_5468_);
lean_closure_set(v___f_5476_, 7, v___x_5474_);
v___x_5477_ = lean_apply_4(v_toBind_5471_, lean_box(0), lean_box(0), v___x_5474_, v___f_5476_);
return v___x_5477_;
}
}
LEAN_EXPORT void l_IO_FS_withIsolatedStreams___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5465_ = stack[0].m_obj;
lean_object* v_inst_5466_ = stack[1].m_obj;
lean_object* v_inst_5467_ = stack[2].m_obj;
lean_object* v_x_5468_ = stack[3].m_obj;
uint8_t v_isolateStderr_5469_ = stack[4].m_num;
lean_object* v_res_5478_;
v_res_5478_ = l_IO_FS_withIsolatedStreams___redArg(v_inst_5465_, v_inst_5466_, v_inst_5467_, v_x_5468_, v_isolateStderr_5469_);
stack->m_obj
 = v_res_5478_;
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___boxed(lean_object* v_inst_5479_, lean_object* v_inst_5480_, lean_object* v_inst_5481_, lean_object* v_x_5482_, lean_object* v_isolateStderr_5483_){
_start:
{
uint8_t v_isolateStderr_boxed_5484_; lean_object* v_res_5485_; 
v_isolateStderr_boxed_5484_ = lean_unbox(v_isolateStderr_5483_);
v_res_5485_ = l_IO_FS_withIsolatedStreams___redArg(v_inst_5479_, v_inst_5480_, v_inst_5481_, v_x_5482_, v_isolateStderr_boxed_5484_);
return v_res_5485_;
}
}
lean_object* l_IO_FS_withIsolatedStreams(lean_object* v_m_5486_, lean_object* v_00_u03b1_5487_, lean_object* v_inst_5488_, lean_object* v_inst_5489_, lean_object* v_inst_5490_, lean_object* v_x_5491_, uint8_t v_isolateStderr_5492_){
_start:
{
lean_object* v___x_5493_; 
v___x_5493_ = l_IO_FS_withIsolatedStreams___redArg(v_inst_5488_, v_inst_5489_, v_inst_5490_, v_x_5491_, v_isolateStderr_5492_);
return v___x_5493_;
}
}
LEAN_EXPORT void l_IO_FS_withIsolatedStreams_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5488_ = stack[2].m_obj;
lean_object* v_inst_5489_ = stack[3].m_obj;
lean_object* v_inst_5490_ = stack[4].m_obj;
lean_object* v_x_5491_ = stack[5].m_obj;
uint8_t v_isolateStderr_5492_ = stack[6].m_num;
lean_object* v_res_5494_;
v_res_5494_ = l_IO_FS_withIsolatedStreams(lean_box(0), lean_box(0), v_inst_5488_, v_inst_5489_, v_inst_5490_, v_x_5491_, v_isolateStderr_5492_);
stack->m_obj
 = v_res_5494_;
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___boxed(lean_object* v_m_5495_, lean_object* v_00_u03b1_5496_, lean_object* v_inst_5497_, lean_object* v_inst_5498_, lean_object* v_inst_5499_, lean_object* v_x_5500_, lean_object* v_isolateStderr_5501_){
_start:
{
uint8_t v_isolateStderr_boxed_5502_; lean_object* v_res_5503_; 
v_isolateStderr_boxed_5502_ = lean_unbox(v_isolateStderr_5501_);
v_res_5503_ = l_IO_FS_withIsolatedStreams(v_m_5495_, v_00_u03b1_5496_, v_inst_5497_, v_inst_5498_, v_inst_5499_, v_x_5500_, v_isolateStderr_boxed_5502_);
return v_res_5503_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9(void){
_start:
{
lean_object* v___x_5560_; lean_object* v___x_5561_; 
v___x_5560_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0));
v___x_5561_ = l_String_toRawSubstring_x27(v___x_5560_);
return v___x_5561_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17(void){
_start:
{
lean_object* v___x_5576_; lean_object* v___x_5577_; 
v___x_5576_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16));
v___x_5577_ = l_String_toRawSubstring_x27(v___x_5576_);
return v___x_5577_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24(void){
_start:
{
lean_object* v___x_5590_; lean_object* v___x_5591_; 
v___x_5590_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18));
v___x_5591_ = l_String_toRawSubstring_x27(v___x_5590_);
return v___x_5591_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31(void){
_start:
{
lean_object* v___x_5606_; lean_object* v___x_5607_; 
v___x_5606_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30));
v___x_5607_ = l_String_toRawSubstring_x27(v___x_5606_);
return v___x_5607_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object* v_x_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_){
_start:
{
lean_object* v___x_5635_; uint8_t v___x_5636_; 
v___x_5635_ = ((lean_object*)(l_termPrintln_x21_____00__closed__1));
lean_inc(v_x_5632_);
v___x_5636_ = l_Lean_Syntax_isOfKind(v_x_5632_, v___x_5635_);
if (v___x_5636_ == 0)
{
lean_object* v___x_5637_; lean_object* v___x_5638_; 
lean_dec(v_x_5632_);
v___x_5637_ = lean_box(1);
v___x_5638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5638_, 0, v___x_5637_);
lean_ctor_set(v___x_5638_, 1, v_a_5634_);
return v___x_5638_;
}
else
{
lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; uint8_t v___x_5642_; 
v___x_5639_ = lean_unsigned_to_nat(1u);
v___x_5640_ = l_Lean_Syntax_getArg(v_x_5632_, v___x_5639_);
lean_dec(v_x_5632_);
v___x_5641_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1));
lean_inc(v___x_5640_);
v___x_5642_ = l_Lean_Syntax_isOfKind(v___x_5640_, v___x_5641_);
if (v___x_5642_ == 0)
{
lean_object* v_quotContext_5643_; lean_object* v_currMacroScope_5644_; lean_object* v_ref_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; 
v_quotContext_5643_ = lean_ctor_get(v_a_5633_, 1);
v_currMacroScope_5644_ = lean_ctor_get(v_a_5633_, 2);
v_ref_5645_ = lean_ctor_get(v_a_5633_, 5);
v___x_5646_ = l_Lean_SourceInfo_fromRef(v_ref_5645_, v___x_5642_);
v___x_5647_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3));
v___x_5648_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5));
v___x_5649_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6));
lean_inc_n(v___x_5646_, 14);
v___x_5650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5650_, 0, v___x_5646_);
lean_ctor_set(v___x_5650_, 1, v___x_5649_);
v___x_5651_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8));
v___x_5652_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
v___x_5653_ = lean_box(0);
lean_inc_n(v_currMacroScope_5644_, 4);
lean_inc_n(v_quotContext_5643_, 4);
v___x_5654_ = l_Lean_addMacroScope(v_quotContext_5643_, v___x_5653_, v_currMacroScope_5644_);
v___x_5655_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15));
v___x_5656_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5656_, 0, v___x_5646_);
lean_ctor_set(v___x_5656_, 1, v___x_5652_);
lean_ctor_set(v___x_5656_, 2, v___x_5654_);
lean_ctor_set(v___x_5656_, 3, v___x_5655_);
v___x_5657_ = l_Lean_Syntax_node1(v___x_5646_, v___x_5651_, v___x_5656_);
v___x_5658_ = l_Lean_Syntax_node2(v___x_5646_, v___x_5648_, v___x_5650_, v___x_5657_);
v___x_5659_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_5660_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
v___x_5661_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20));
v___x_5662_ = l_Lean_addMacroScope(v_quotContext_5643_, v___x_5661_, v_currMacroScope_5644_);
v___x_5663_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22));
v___x_5664_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5646_);
lean_ctor_set(v___x_5664_, 1, v___x_5660_);
lean_ctor_set(v___x_5664_, 2, v___x_5662_);
lean_ctor_set(v___x_5664_, 3, v___x_5663_);
v___x_5665_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_5666_ = l_Lean_Syntax_node1(v___x_5646_, v___x_5665_, v___x_5640_);
v___x_5667_ = l_Lean_Syntax_node2(v___x_5646_, v___x_5659_, v___x_5664_, v___x_5666_);
v___x_5668_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23));
v___x_5669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5669_, 0, v___x_5646_);
lean_ctor_set(v___x_5669_, 1, v___x_5668_);
v___x_5670_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
v___x_5671_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25));
v___x_5672_ = l_Lean_addMacroScope(v_quotContext_5643_, v___x_5671_, v_currMacroScope_5644_);
v___x_5673_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29));
v___x_5674_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5646_);
lean_ctor_set(v___x_5674_, 1, v___x_5670_);
lean_ctor_set(v___x_5674_, 2, v___x_5672_);
lean_ctor_set(v___x_5674_, 3, v___x_5673_);
v___x_5675_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
v___x_5676_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32));
v___x_5677_ = l_Lean_addMacroScope(v_quotContext_5643_, v___x_5676_, v_currMacroScope_5644_);
v___x_5678_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36));
v___x_5679_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5679_, 0, v___x_5646_);
lean_ctor_set(v___x_5679_, 1, v___x_5675_);
lean_ctor_set(v___x_5679_, 2, v___x_5677_);
lean_ctor_set(v___x_5679_, 3, v___x_5678_);
v___x_5680_ = l_Lean_Syntax_node1(v___x_5646_, v___x_5665_, v___x_5679_);
v___x_5681_ = l_Lean_Syntax_node2(v___x_5646_, v___x_5659_, v___x_5674_, v___x_5680_);
v___x_5682_ = l_Lean_Syntax_node1(v___x_5646_, v___x_5665_, v___x_5681_);
v___x_5683_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37));
v___x_5684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5646_);
lean_ctor_set(v___x_5684_, 1, v___x_5683_);
v___x_5685_ = l_Lean_Syntax_node5(v___x_5646_, v___x_5647_, v___x_5658_, v___x_5667_, v___x_5669_, v___x_5682_, v___x_5684_);
v___x_5686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5685_);
lean_ctor_set(v___x_5686_, 1, v_a_5634_);
return v___x_5686_;
}
else
{
lean_object* v_quotContext_5687_; lean_object* v_currMacroScope_5688_; lean_object* v_ref_5689_; uint8_t v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; 
v_quotContext_5687_ = lean_ctor_get(v_a_5633_, 1);
v_currMacroScope_5688_ = lean_ctor_get(v_a_5633_, 2);
v_ref_5689_ = lean_ctor_get(v_a_5633_, 5);
v___x_5690_ = 0;
v___x_5691_ = l_Lean_SourceInfo_fromRef(v_ref_5689_, v___x_5690_);
v___x_5692_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3));
v___x_5693_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5));
v___x_5694_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6));
lean_inc_n(v___x_5691_, 17);
v___x_5695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5695_, 0, v___x_5691_);
lean_ctor_set(v___x_5695_, 1, v___x_5694_);
v___x_5696_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8));
v___x_5697_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
v___x_5698_ = lean_box(0);
lean_inc_n(v_currMacroScope_5688_, 4);
lean_inc_n(v_quotContext_5687_, 4);
v___x_5699_ = l_Lean_addMacroScope(v_quotContext_5687_, v___x_5698_, v_currMacroScope_5688_);
v___x_5700_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15));
v___x_5701_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5701_, 0, v___x_5691_);
lean_ctor_set(v___x_5701_, 1, v___x_5697_);
lean_ctor_set(v___x_5701_, 2, v___x_5699_);
lean_ctor_set(v___x_5701_, 3, v___x_5700_);
v___x_5702_ = l_Lean_Syntax_node1(v___x_5691_, v___x_5696_, v___x_5701_);
v___x_5703_ = l_Lean_Syntax_node2(v___x_5691_, v___x_5693_, v___x_5695_, v___x_5702_);
v___x_5704_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_5705_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
v___x_5706_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20));
v___x_5707_ = l_Lean_addMacroScope(v_quotContext_5687_, v___x_5706_, v_currMacroScope_5688_);
v___x_5708_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22));
v___x_5709_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5691_);
lean_ctor_set(v___x_5709_, 1, v___x_5705_);
lean_ctor_set(v___x_5709_, 2, v___x_5707_);
lean_ctor_set(v___x_5709_, 3, v___x_5708_);
v___x_5710_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_5711_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39));
v___x_5712_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41));
v___x_5713_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42));
v___x_5714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5691_);
lean_ctor_set(v___x_5714_, 1, v___x_5713_);
v___x_5715_ = l_Lean_Syntax_node2(v___x_5691_, v___x_5712_, v___x_5714_, v___x_5640_);
v___x_5716_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37));
v___x_5717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5691_);
lean_ctor_set(v___x_5717_, 1, v___x_5716_);
lean_inc_ref(v___x_5717_);
lean_inc(v___x_5703_);
v___x_5718_ = l_Lean_Syntax_node3(v___x_5691_, v___x_5711_, v___x_5703_, v___x_5715_, v___x_5717_);
v___x_5719_ = l_Lean_Syntax_node1(v___x_5691_, v___x_5710_, v___x_5718_);
v___x_5720_ = l_Lean_Syntax_node2(v___x_5691_, v___x_5704_, v___x_5709_, v___x_5719_);
v___x_5721_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23));
v___x_5722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5722_, 0, v___x_5691_);
lean_ctor_set(v___x_5722_, 1, v___x_5721_);
v___x_5723_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
v___x_5724_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25));
v___x_5725_ = l_Lean_addMacroScope(v_quotContext_5687_, v___x_5724_, v_currMacroScope_5688_);
v___x_5726_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29));
v___x_5727_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5727_, 0, v___x_5691_);
lean_ctor_set(v___x_5727_, 1, v___x_5723_);
lean_ctor_set(v___x_5727_, 2, v___x_5725_);
lean_ctor_set(v___x_5727_, 3, v___x_5726_);
v___x_5728_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
v___x_5729_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32));
v___x_5730_ = l_Lean_addMacroScope(v_quotContext_5687_, v___x_5729_, v_currMacroScope_5688_);
v___x_5731_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36));
v___x_5732_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5691_);
lean_ctor_set(v___x_5732_, 1, v___x_5728_);
lean_ctor_set(v___x_5732_, 2, v___x_5730_);
lean_ctor_set(v___x_5732_, 3, v___x_5731_);
v___x_5733_ = l_Lean_Syntax_node1(v___x_5691_, v___x_5710_, v___x_5732_);
v___x_5734_ = l_Lean_Syntax_node2(v___x_5691_, v___x_5704_, v___x_5727_, v___x_5733_);
v___x_5735_ = l_Lean_Syntax_node1(v___x_5691_, v___x_5710_, v___x_5734_);
v___x_5736_ = l_Lean_Syntax_node5(v___x_5691_, v___x_5692_, v___x_5703_, v___x_5720_, v___x_5722_, v___x_5735_, v___x_5717_);
v___x_5737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5737_, 0, v___x_5736_);
lean_ctor_set(v___x_5737_, 1, v_a_5634_);
return v___x_5737_;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___boxed(lean_object* v_x_5738_, lean_object* v_a_5739_, lean_object* v_a_5740_){
_start:
{
lean_object* v_res_5741_; 
v_res_5741_ = l___aux__Init__System__IO______macroRules__termPrintln_x21______1(v_x_5738_, v_a_5739_, v_a_5740_);
lean_dec_ref(v_a_5739_);
return v_res_5741_;
}
}
LEAN_EXPORT void l_Runtime_markMultiThreaded_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5743_ = stack[1].m_obj;
lean_object* v_res_5745_;
v_res_5745_ = lean_runtime_mark_multi_threaded(v_a_5743_);
stack->m_obj
 = v_res_5745_;
}
LEAN_EXPORT lean_object* l_Runtime_markMultiThreaded___boxed(lean_object* v_00_u03b1_5746_, lean_object* v_a_5747_, lean_object* v_a_00___x40___internal___hyg_5748_){
_start:
{
lean_object* v_res_5749_; 
v_res_5749_ = lean_runtime_mark_multi_threaded(v_a_5747_);
return v_res_5749_;
}
}
LEAN_EXPORT void l_Runtime_markPersistent_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5751_ = stack[1].m_obj;
lean_object* v_res_5753_;
v_res_5753_ = lean_runtime_mark_persistent(v_a_5751_);
stack->m_obj
 = v_res_5753_;
}
LEAN_EXPORT lean_object* l_Runtime_markPersistent___boxed(lean_object* v_00_u03b1_5754_, lean_object* v_a_5755_, lean_object* v_a_00___x40___internal___hyg_5756_){
_start:
{
lean_object* v_res_5757_; 
v_res_5757_ = lean_runtime_mark_persistent(v_a_5755_);
return v_res_5757_;
}
}
LEAN_EXPORT void l_Runtime_forget_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5759_ = stack[1].m_obj;
lean_object* v_res_5761_;
v_res_5761_ = lean_runtime_forget(v_a_5759_);
stack->m_obj
 = v_res_5761_;
}
LEAN_EXPORT lean_object* l_Runtime_forget___boxed(lean_object* v_00_u03b1_5762_, lean_object* v_a_5763_, lean_object* v_a_00___x40___internal___hyg_5764_){
_start:
{
lean_object* v_res_5765_; 
v_res_5765_ = lean_runtime_forget(v_a_5763_);
return v_res_5765_;
}
}
LEAN_EXPORT void l_Runtime_hold_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5767_ = stack[1].m_obj;
lean_object* v_res_5769_;
v_res_5769_ = lean_runtime_hold(v_a_5767_);
stack->m_obj
 = v_res_5769_;
}
LEAN_EXPORT lean_object* l_Runtime_hold___boxed(lean_object* v_00_u03b1_5770_, lean_object* v_a_5771_, lean_object* v_a_00___x40___internal___hyg_5772_){
_start:
{
lean_object* v_res_5773_; 
v_res_5773_ = lean_runtime_hold(v_a_5771_);
lean_dec(v_a_5771_);
return v_res_5773_;
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
