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
lean_dec_ref_known(v_a_2514_, 2);
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
lean_dec_ref_known(v_a_2757_, 1);
v_a_2753_ = v_val_2761_;
goto _start;
}
else
{
lean_object* v_val_2763_; lean_object* v___x_2765_; 
lean_dec_ref(v_f_2754_);
v_val_2763_ = lean_ctor_get(v_a_2757_, 0);
lean_inc(v_val_2763_);
lean_dec_ref_known(v_a_2757_, 1);
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
lean_dec_ref_known(v___x_2924_, 1);
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
lean_dec_ref_known(v___x_2946_, 1);
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
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3101_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3049_ = v___x_3046_;
v_isShared_3050_ = v_isSharedCheck_3101_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3101_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___y_3052_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; uint32_t v___y_3059_; uint32_t v___y_3067_; lean_object* v___x_3089_; lean_object* v___x_3090_; uint8_t v___x_3091_; 
v___x_3089_ = lean_string_utf8_byte_size(v_a_3047_);
v___x_3090_ = lean_unsigned_to_nat(0u);
v___x_3091_ = lean_nat_dec_eq(v___x_3089_, v___x_3090_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_inc(v_a_3047_);
v___x_3092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3092_, 0, v_a_3047_);
lean_ctor_set(v___x_3092_, 1, v___x_3090_);
lean_ctor_set(v___x_3092_, 2, v___x_3089_);
v___x_3093_ = l_String_Slice_Pos_prev_x3f(v___x_3092_, v___x_3089_);
if (lean_obj_tag(v___x_3093_) == 0)
{
uint32_t v___x_3094_; 
lean_dec_ref_known(v___x_3092_, 3);
v___x_3094_ = 65;
v___y_3067_ = v___x_3094_;
goto v___jp_3066_;
}
else
{
lean_object* v_val_3095_; lean_object* v___x_3096_; 
v_val_3095_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_val_3095_);
lean_dec_ref_known(v___x_3093_, 1);
v___x_3096_ = l_String_Slice_Pos_get_x3f(v___x_3092_, v_val_3095_);
lean_dec(v_val_3095_);
lean_dec_ref_known(v___x_3092_, 3);
if (lean_obj_tag(v___x_3096_) == 0)
{
uint32_t v___x_3097_; 
v___x_3097_ = 65;
v___y_3067_ = v___x_3097_;
goto v___jp_3066_;
}
else
{
lean_object* v_val_3098_; uint32_t v___x_3099_; 
v_val_3098_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_val_3098_);
lean_dec_ref_known(v___x_3096_, 1);
v___x_3099_ = lean_unbox_uint32(v_val_3098_);
lean_dec(v_val_3098_);
v___y_3067_ = v___x_3099_;
goto v___jp_3066_;
}
}
}
else
{
lean_object* v___x_3100_; 
lean_del_object(v___x_3049_);
lean_dec(v_a_3047_);
v___x_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3100_, 0, v_lines_3044_);
return v___x_3100_;
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
lean_dec(v___y_3057_);
v___y_3052_ = v___y_3056_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3062_ = lean_string_utf8_byte_size(v___y_3056_);
lean_inc(v___y_3058_);
lean_inc_ref(v___y_3056_);
v___x_3063_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3063_, 0, v___y_3056_);
lean_ctor_set(v___x_3063_, 1, v___y_3058_);
lean_ctor_set(v___x_3063_, 2, v___x_3062_);
v___x_3064_ = l_String_Slice_Pos_prevn(v___x_3063_, v___x_3062_, v___y_3057_);
lean_dec_ref_known(v___x_3063_, 3);
v___x_3065_ = lean_string_utf8_extract(v___y_3056_, v___y_3058_, v___x_3064_);
lean_dec(v___x_3064_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3056_);
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
lean_dec_ref_known(v___x_3077_, 3);
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
lean_dec_ref_known(v___x_3081_, 3);
v___x_3083_ = 65;
v___y_3056_ = v___x_3079_;
v___y_3057_ = v___x_3074_;
v___y_3058_ = v___x_3075_;
v___y_3059_ = v___x_3083_;
goto v___jp_3055_;
}
else
{
lean_object* v_val_3084_; lean_object* v___x_3085_; 
v_val_3084_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_val_3084_);
lean_dec_ref_known(v___x_3082_, 1);
v___x_3085_ = l_String_Slice_Pos_get_x3f(v___x_3081_, v_val_3084_);
lean_dec(v_val_3084_);
lean_dec_ref_known(v___x_3081_, 3);
if (lean_obj_tag(v___x_3085_) == 0)
{
uint32_t v___x_3086_; 
v___x_3086_ = 65;
v___y_3056_ = v___x_3079_;
v___y_3057_ = v___x_3074_;
v___y_3058_ = v___x_3075_;
v___y_3059_ = v___x_3086_;
goto v___jp_3055_;
}
else
{
lean_object* v_val_3087_; uint32_t v___x_3088_; 
v_val_3087_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_val_3087_);
lean_dec_ref_known(v___x_3085_, 1);
v___x_3088_ = lean_unbox_uint32(v_val_3087_);
lean_dec(v_val_3087_);
v___y_3056_ = v___x_3079_;
v___y_3057_ = v___x_3074_;
v___y_3058_ = v___x_3075_;
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
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec_ref(v_lines_3044_);
v_a_3102_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3046_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3046_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Handle_lines_read___boxed(lean_object* v_h_3110_, lean_object* v_lines_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_3110_, v_lines_3111_);
lean_dec(v_h_3110_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines(lean_object* v_h_3116_){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_3119_ = l___private_Init_System_IO_0__IO_FS_Handle_lines_read(v_h_3116_, v___x_3118_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Handle_lines___boxed(lean_object* v_h_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_IO_FS_Handle_lines(v_h_3120_);
lean_dec(v_h_3120_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines(lean_object* v_fname_3123_){
_start:
{
uint8_t v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = 0;
v___x_3126_ = lean_io_prim_handle_mk(v_fname_3123_, v___x_3125_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3128_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref_known(v___x_3126_, 1);
v___x_3128_ = l_IO_FS_Handle_lines(v_a_3127_);
lean_dec(v_a_3127_);
return v___x_3128_;
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
v_a_3129_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3126_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3126_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_lines___boxed(lean_object* v_fname_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_IO_FS_lines(v_fname_3137_);
lean_dec_ref(v_fname_3137_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile(lean_object* v_fname_3140_, lean_object* v_content_3141_){
_start:
{
uint8_t v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = 1;
v___x_3144_ = lean_io_prim_handle_mk(v_fname_3140_, v___x_3143_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3146_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
v___x_3146_ = lean_io_prim_handle_write(v_a_3145_, v_content_3141_);
lean_dec(v_a_3145_);
return v___x_3146_;
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
v_a_3147_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3144_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3144_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
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
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeBinFile___boxed(lean_object* v_fname_3155_, lean_object* v_content_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_IO_FS_writeBinFile(v_fname_3155_, v_content_3156_);
lean_dec_ref(v_content_3156_);
lean_dec_ref(v_fname_3155_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile(lean_object* v_fname_3159_, lean_object* v_content_3160_){
_start:
{
uint8_t v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = 1;
v___x_3163_ = lean_io_prim_handle_mk(v_fname_3159_, v___x_3162_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3165_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v___x_3165_ = lean_io_prim_handle_put_str(v_a_3164_, v_content_3160_);
lean_dec(v_a_3164_);
return v___x_3165_;
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
v_a_3166_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3163_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3163_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_writeFile___boxed(lean_object* v_fname_3174_, lean_object* v_content_3175_, lean_object* v_a_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_IO_FS_writeFile(v_fname_3174_, v_content_3175_);
lean_dec_ref(v_content_3175_);
lean_dec_ref(v_fname_3174_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn(lean_object* v_strm_3178_, lean_object* v_s_3179_){
_start:
{
lean_object* v_putStr_3181_; uint32_t v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v_putStr_3181_ = lean_ctor_get(v_strm_3178_, 4);
lean_inc_ref(v_putStr_3181_);
lean_dec_ref(v_strm_3178_);
v___x_3182_ = 10;
v___x_3183_ = lean_string_push(v_s_3179_, v___x_3182_);
v___x_3184_ = lean_apply_2(v_putStr_3181_, v___x_3183_, lean_box(0));
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_putStrLn___boxed(lean_object* v_strm_3185_, lean_object* v_s_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_IO_FS_Stream_putStrLn(v_strm_3185_, v_s_3186_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00IO_FS_instReprDirEntry_repr_spec__0(lean_object* v_a_3189_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = lean_nat_to_int(v_a_3189_);
return v___x_3190_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = lean_unsigned_to_nat(8u);
v___x_3205_ = lean_nat_to_int(v___x_3204_);
return v___x_3205_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = lean_unsigned_to_nat(12u);
v___x_3216_ = lean_nat_to_int(v___x_3215_);
return v___x_3216_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__0));
v___x_3219_ = lean_string_length(v___x_3218_);
return v___x_3219_;
}
}
static lean_object* _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__16, &l_IO_FS_instReprDirEntry_repr___redArg___closed__16_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__16);
v___x_3221_ = lean_nat_to_int(v___x_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___redArg(lean_object* v_x_3226_){
_start:
{
lean_object* v_root_3227_; lean_object* v_fileName_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3267_; 
v_root_3227_ = lean_ctor_get(v_x_3226_, 0);
v_fileName_3228_ = lean_ctor_get(v_x_3226_, 1);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_x_3226_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3230_ = v_x_3226_;
v_isShared_3231_ = v_isSharedCheck_3267_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_fileName_3228_);
lean_inc(v_root_3227_);
lean_dec(v_x_3226_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3267_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
v___x_3232_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3233_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__6));
v___x_3234_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3235_ = lean_unsigned_to_nat(0u);
v___x_3236_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__9));
v___x_3237_ = l_String_quote(v_root_3227_);
v___x_3238_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set_tag(v___x_3230_, 5);
lean_ctor_set(v___x_3230_, 1, v___x_3238_);
lean_ctor_set(v___x_3230_, 0, v___x_3236_);
v___x_3240_ = v___x_3230_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; uint8_t v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3241_ = l_Repr_addAppParen(v___x_3240_, v___x_3235_);
v___x_3242_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3234_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = 0;
v___x_3244_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set_uint8(v___x_3244_, sizeof(void*)*1, v___x_3243_);
v___x_3245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3233_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = lean_box(1);
v___x_3249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__13));
v___x_3251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3251_);
lean_ctor_set(v___x_3252_, 1, v___x_3232_);
v___x_3253_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__14, &l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14);
v___x_3254_ = l_String_quote(v_fileName_3228_);
v___x_3255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
v___x_3256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3253_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
lean_ctor_set_uint8(v___x_3257_, sizeof(void*)*1, v___x_3243_);
v___x_3258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3252_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v___x_3259_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3260_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
lean_ctor_set(v___x_3261_, 1, v___x_3258_);
v___x_3262_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3261_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3259_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*1, v___x_3243_);
return v___x_3265_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr(lean_object* v_x_3268_, lean_object* v_prec_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_IO_FS_instReprDirEntry_repr___redArg(v_x_3268_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprDirEntry_repr___boxed(lean_object* v_x_3271_, lean_object* v_prec_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_IO_FS_instReprDirEntry_repr(v_x_3271_, v_prec_3272_);
lean_dec(v_prec_3272_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_DirEntry_path(lean_object* v_entry_3276_){
_start:
{
lean_object* v_root_3277_; lean_object* v_fileName_3278_; lean_object* v___x_3279_; 
v_root_3277_ = lean_ctor_get(v_entry_3276_, 0);
lean_inc_ref(v_root_3277_);
v_fileName_3278_ = lean_ctor_get(v_entry_3276_, 1);
lean_inc_ref(v_fileName_3278_);
lean_dec_ref(v_entry_3276_);
v___x_3279_ = l_System_FilePath_join(v_root_3277_, v_fileName_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx(uint8_t v_x_3280_){
_start:
{
switch(v_x_3280_)
{
case 0:
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_unsigned_to_nat(0u);
return v___x_3281_;
}
case 1:
{
lean_object* v___x_3282_; 
v___x_3282_ = lean_unsigned_to_nat(1u);
return v___x_3282_;
}
case 2:
{
lean_object* v___x_3283_; 
v___x_3283_ = lean_unsigned_to_nat(2u);
return v___x_3283_;
}
default: 
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_unsigned_to_nat(3u);
return v___x_3284_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorIdx___boxed(lean_object* v_x_3285_){
_start:
{
uint8_t v_x_boxed_3286_; lean_object* v_res_3287_; 
v_x_boxed_3286_ = lean_unbox(v_x_3285_);
v_res_3287_ = l_IO_FS_FileType_ctorIdx(v_x_boxed_3286_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx(uint8_t v_x_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_IO_FS_FileType_ctorIdx(v_x_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_toCtorIdx___boxed(lean_object* v_x_3290_){
_start:
{
uint8_t v_x_4__boxed_3291_; lean_object* v_res_3292_; 
v_x_4__boxed_3291_ = lean_unbox(v_x_3290_);
v_res_3292_ = l_IO_FS_FileType_toCtorIdx(v_x_4__boxed_3291_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg(lean_object* v_k_3293_){
_start:
{
lean_inc(v_k_3293_);
return v_k_3293_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___redArg___boxed(lean_object* v_k_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_IO_FS_FileType_ctorElim___redArg(v_k_3294_);
lean_dec(v_k_3294_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim(lean_object* v_motive_3296_, lean_object* v_ctorIdx_3297_, uint8_t v_t_3298_, lean_object* v_h_3299_, lean_object* v_k_3300_){
_start:
{
lean_inc(v_k_3300_);
return v_k_3300_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_ctorElim___boxed(lean_object* v_motive_3301_, lean_object* v_ctorIdx_3302_, lean_object* v_t_3303_, lean_object* v_h_3304_, lean_object* v_k_3305_){
_start:
{
uint8_t v_t_boxed_3306_; lean_object* v_res_3307_; 
v_t_boxed_3306_ = lean_unbox(v_t_3303_);
v_res_3307_ = l_IO_FS_FileType_ctorElim(v_motive_3301_, v_ctorIdx_3302_, v_t_boxed_3306_, v_h_3304_, v_k_3305_);
lean_dec(v_k_3305_);
lean_dec(v_ctorIdx_3302_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg(lean_object* v_dir_3308_){
_start:
{
lean_inc(v_dir_3308_);
return v_dir_3308_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___redArg___boxed(lean_object* v_dir_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_IO_FS_FileType_dir_elim___redArg(v_dir_3309_);
lean_dec(v_dir_3309_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim(lean_object* v_motive_3311_, uint8_t v_t_3312_, lean_object* v_h_3313_, lean_object* v_dir_3314_){
_start:
{
lean_inc(v_dir_3314_);
return v_dir_3314_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_dir_elim___boxed(lean_object* v_motive_3315_, lean_object* v_t_3316_, lean_object* v_h_3317_, lean_object* v_dir_3318_){
_start:
{
uint8_t v_t_boxed_3319_; lean_object* v_res_3320_; 
v_t_boxed_3319_ = lean_unbox(v_t_3316_);
v_res_3320_ = l_IO_FS_FileType_dir_elim(v_motive_3315_, v_t_boxed_3319_, v_h_3317_, v_dir_3318_);
lean_dec(v_dir_3318_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg(lean_object* v_file_3321_){
_start:
{
lean_inc(v_file_3321_);
return v_file_3321_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___redArg___boxed(lean_object* v_file_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_IO_FS_FileType_file_elim___redArg(v_file_3322_);
lean_dec(v_file_3322_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim(lean_object* v_motive_3324_, uint8_t v_t_3325_, lean_object* v_h_3326_, lean_object* v_file_3327_){
_start:
{
lean_inc(v_file_3327_);
return v_file_3327_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_file_elim___boxed(lean_object* v_motive_3328_, lean_object* v_t_3329_, lean_object* v_h_3330_, lean_object* v_file_3331_){
_start:
{
uint8_t v_t_boxed_3332_; lean_object* v_res_3333_; 
v_t_boxed_3332_ = lean_unbox(v_t_3329_);
v_res_3333_ = l_IO_FS_FileType_file_elim(v_motive_3328_, v_t_boxed_3332_, v_h_3330_, v_file_3331_);
lean_dec(v_file_3331_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg(lean_object* v_symlink_3334_){
_start:
{
lean_inc(v_symlink_3334_);
return v_symlink_3334_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___redArg___boxed(lean_object* v_symlink_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_IO_FS_FileType_symlink_elim___redArg(v_symlink_3335_);
lean_dec(v_symlink_3335_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim(lean_object* v_motive_3337_, uint8_t v_t_3338_, lean_object* v_h_3339_, lean_object* v_symlink_3340_){
_start:
{
lean_inc(v_symlink_3340_);
return v_symlink_3340_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_symlink_elim___boxed(lean_object* v_motive_3341_, lean_object* v_t_3342_, lean_object* v_h_3343_, lean_object* v_symlink_3344_){
_start:
{
uint8_t v_t_boxed_3345_; lean_object* v_res_3346_; 
v_t_boxed_3345_ = lean_unbox(v_t_3342_);
v_res_3346_ = l_IO_FS_FileType_symlink_elim(v_motive_3341_, v_t_boxed_3345_, v_h_3343_, v_symlink_3344_);
lean_dec(v_symlink_3344_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg(lean_object* v_other_3347_){
_start:
{
lean_inc(v_other_3347_);
return v_other_3347_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___redArg___boxed(lean_object* v_other_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_IO_FS_FileType_other_elim___redArg(v_other_3348_);
lean_dec(v_other_3348_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim(lean_object* v_motive_3350_, uint8_t v_t_3351_, lean_object* v_h_3352_, lean_object* v_other_3353_){
_start:
{
lean_inc(v_other_3353_);
return v_other_3353_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_FileType_other_elim___boxed(lean_object* v_motive_3354_, lean_object* v_t_3355_, lean_object* v_h_3356_, lean_object* v_other_3357_){
_start:
{
uint8_t v_t_boxed_3358_; lean_object* v_res_3359_; 
v_t_boxed_3358_ = lean_unbox(v_t_3355_);
v_res_3359_ = l_IO_FS_FileType_other_elim(v_motive_3354_, v_t_boxed_3358_, v_h_3356_, v_other_3357_);
lean_dec(v_other_3357_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr(uint8_t v_x_3372_, lean_object* v_prec_3373_){
_start:
{
lean_object* v___y_3375_; lean_object* v___y_3382_; lean_object* v___y_3389_; lean_object* v___y_3396_; 
switch(v_x_3372_)
{
case 0:
{
lean_object* v___x_3402_; uint8_t v___x_3403_; 
v___x_3402_ = lean_unsigned_to_nat(1024u);
v___x_3403_ = lean_nat_dec_le(v___x_3402_, v_prec_3373_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3375_ = v___x_3404_;
goto v___jp_3374_;
}
else
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3375_ = v___x_3405_;
goto v___jp_3374_;
}
}
case 1:
{
lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3406_ = lean_unsigned_to_nat(1024u);
v___x_3407_ = lean_nat_dec_le(v___x_3406_, v_prec_3373_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; 
v___x_3408_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3382_ = v___x_3408_;
goto v___jp_3381_;
}
else
{
lean_object* v___x_3409_; 
v___x_3409_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3382_ = v___x_3409_;
goto v___jp_3381_;
}
}
case 2:
{
lean_object* v___x_3410_; uint8_t v___x_3411_; 
v___x_3410_ = lean_unsigned_to_nat(1024u);
v___x_3411_ = lean_nat_dec_le(v___x_3410_, v_prec_3373_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; 
v___x_3412_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3389_ = v___x_3412_;
goto v___jp_3388_;
}
else
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3389_ = v___x_3413_;
goto v___jp_3388_;
}
}
default: 
{
lean_object* v___x_3414_; uint8_t v___x_3415_; 
v___x_3414_ = lean_unsigned_to_nat(1024u);
v___x_3415_ = lean_nat_dec_le(v___x_3414_, v_prec_3373_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__6, &l_IO_instReprTaskState_repr___closed__6_once, _init_l_IO_instReprTaskState_repr___closed__6);
v___y_3396_ = v___x_3416_;
goto v___jp_3395_;
}
else
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_obj_once(&l_IO_instReprTaskState_repr___closed__7, &l_IO_instReprTaskState_repr___closed__7_once, _init_l_IO_instReprTaskState_repr___closed__7);
v___y_3396_ = v___x_3417_;
goto v___jp_3395_;
}
}
}
v___jp_3374_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; uint8_t v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3376_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__1));
lean_inc(v___y_3375_);
v___x_3377_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___y_3375_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = 0;
v___x_3379_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3379_, 0, v___x_3377_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*1, v___x_3378_);
v___x_3380_ = l_Repr_addAppParen(v___x_3379_, v_prec_3373_);
return v___x_3380_;
}
v___jp_3381_:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; uint8_t v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3383_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__3));
lean_inc(v___y_3382_);
v___x_3384_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___y_3382_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = 0;
v___x_3386_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3386_, 0, v___x_3384_);
lean_ctor_set_uint8(v___x_3386_, sizeof(void*)*1, v___x_3385_);
v___x_3387_ = l_Repr_addAppParen(v___x_3386_, v_prec_3373_);
return v___x_3387_;
}
v___jp_3388_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3390_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__5));
lean_inc(v___y_3389_);
v___x_3391_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___y_3389_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v___x_3392_ = 0;
v___x_3393_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3393_, 0, v___x_3391_);
lean_ctor_set_uint8(v___x_3393_, sizeof(void*)*1, v___x_3392_);
v___x_3394_ = l_Repr_addAppParen(v___x_3393_, v_prec_3373_);
return v___x_3394_;
}
v___jp_3395_:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3397_ = ((lean_object*)(l_IO_FS_instReprFileType_repr___closed__7));
lean_inc(v___y_3396_);
v___x_3398_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___y_3396_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = 0;
v___x_3400_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3400_, 0, v___x_3398_);
lean_ctor_set_uint8(v___x_3400_, sizeof(void*)*1, v___x_3399_);
v___x_3401_ = l_Repr_addAppParen(v___x_3400_, v_prec_3373_);
return v___x_3401_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprFileType_repr___boxed(lean_object* v_x_3418_, lean_object* v_prec_3419_){
_start:
{
uint8_t v_x_229__boxed_3420_; lean_object* v_res_3421_; 
v_x_229__boxed_3420_ = lean_unbox(v_x_3418_);
v_res_3421_ = l_IO_FS_instReprFileType_repr(v_x_229__boxed_3420_, v_prec_3419_);
lean_dec(v_prec_3419_);
return v_res_3421_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instBEqFileType_beq(uint8_t v_x_3424_, uint8_t v_y_3425_){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3426_ = l_IO_FS_FileType_ctorIdx(v_x_3424_);
v___x_3427_ = l_IO_FS_FileType_ctorIdx(v_y_3425_);
v___x_3428_ = lean_nat_dec_eq(v___x_3426_, v___x_3427_);
lean_dec(v___x_3427_);
lean_dec(v___x_3426_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instBEqFileType_beq___boxed(lean_object* v_x_3429_, lean_object* v_y_3430_){
_start:
{
uint8_t v_x_17__boxed_3431_; uint8_t v_y_18__boxed_3432_; uint8_t v_res_3433_; lean_object* v_r_3434_; 
v_x_17__boxed_3431_ = lean_unbox(v_x_3429_);
v_y_18__boxed_3432_ = lean_unbox(v_y_3430_);
v_res_3433_ = l_IO_FS_instBEqFileType_beq(v_x_17__boxed_3431_, v_y_18__boxed_3432_);
v_r_3434_ = lean_box(v_res_3433_);
return v_r_3434_;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = lean_unsigned_to_nat(7u);
v___x_3447_ = lean_nat_to_int(v___x_3446_);
return v___x_3447_;
}
}
static lean_object* _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3451_ = lean_unsigned_to_nat(0u);
v___x_3452_ = lean_nat_to_int(v___x_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg(lean_object* v_x_3453_){
_start:
{
lean_object* v_sec_3454_; uint32_t v_nsec_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___y_3460_; lean_object* v___x_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; 
v_sec_3454_ = lean_ctor_get(v_x_3453_, 0);
v_nsec_3455_ = lean_ctor_get_uint32(v_x_3453_, sizeof(void*)*1);
v___x_3456_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3457_ = ((lean_object*)(l_IO_FS_instReprSystemTime_repr___redArg___closed__3));
v___x_3458_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__4, &l_IO_FS_instReprSystemTime_repr___redArg___closed__4_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__4);
v___x_3486_ = lean_unsigned_to_nat(0u);
v___x_3487_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__7, &l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7);
v___x_3488_ = lean_int_dec_lt(v_sec_3454_, v___x_3487_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = l_Int_repr(v_sec_3454_);
v___x_3490_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
v___y_3460_ = v___x_3490_;
goto v___jp_3459_;
}
else
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3491_ = l_Int_repr(v_sec_3454_);
v___x_3492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
v___x_3493_ = l_Repr_addAppParen(v___x_3492_, v___x_3486_);
v___y_3460_ = v___x_3493_;
goto v___jp_3459_;
}
v___jp_3459_:
{
lean_object* v___x_3461_; uint8_t v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3461_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3458_);
lean_ctor_set(v___x_3461_, 1, v___y_3460_);
v___x_3462_ = 0;
v___x_3463_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3463_, 0, v___x_3461_);
lean_ctor_set_uint8(v___x_3463_, sizeof(void*)*1, v___x_3462_);
v___x_3464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3457_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = lean_box(1);
v___x_3468_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3466_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = ((lean_object*)(l_IO_FS_instReprSystemTime_repr___redArg___closed__6));
v___x_3470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3468_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
lean_ctor_set(v___x_3471_, 1, v___x_3456_);
v___x_3472_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3473_ = lean_uint32_to_nat(v_nsec_3455_);
v___x_3474_ = l_Nat_reprFast(v___x_3473_);
v___x_3475_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
v___x_3476_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3472_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
lean_ctor_set_uint8(v___x_3477_, sizeof(void*)*1, v___x_3462_);
v___x_3478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3471_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3480_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
lean_ctor_set(v___x_3481_, 1, v___x_3478_);
v___x_3482_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3483_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3479_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
v___x_3485_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
lean_ctor_set_uint8(v___x_3485_, sizeof(void*)*1, v___x_3462_);
return v___x_3485_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___redArg___boxed(lean_object* v_x_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_3494_);
lean_dec_ref(v_x_3494_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr(lean_object* v_x_3496_, lean_object* v_prec_3497_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_IO_FS_instReprSystemTime_repr___redArg(v_x_3496_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprSystemTime_repr___boxed(lean_object* v_x_3499_, lean_object* v_prec_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_IO_FS_instReprSystemTime_repr(v_x_3499_, v_prec_3500_);
lean_dec(v_prec_3500_);
lean_dec_ref(v_x_3499_);
return v_res_3501_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instBEqSystemTime_beq(lean_object* v_x_3504_, lean_object* v_x_3505_){
_start:
{
lean_object* v_sec_3506_; uint32_t v_nsec_3507_; lean_object* v_sec_3508_; uint32_t v_nsec_3509_; uint8_t v___x_3510_; 
v_sec_3506_ = lean_ctor_get(v_x_3504_, 0);
v_nsec_3507_ = lean_ctor_get_uint32(v_x_3504_, sizeof(void*)*1);
v_sec_3508_ = lean_ctor_get(v_x_3505_, 0);
v_nsec_3509_ = lean_ctor_get_uint32(v_x_3505_, sizeof(void*)*1);
v___x_3510_ = lean_int_dec_eq(v_sec_3506_, v_sec_3508_);
if (v___x_3510_ == 0)
{
return v___x_3510_;
}
else
{
uint8_t v___x_3511_; 
v___x_3511_ = lean_uint32_dec_eq(v_nsec_3507_, v_nsec_3509_);
return v___x_3511_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_instBEqSystemTime_beq___boxed(lean_object* v_x_3512_, lean_object* v_x_3513_){
_start:
{
uint8_t v_res_3514_; lean_object* v_r_3515_; 
v_res_3514_ = l_IO_FS_instBEqSystemTime_beq(v_x_3512_, v_x_3513_);
lean_dec_ref(v_x_3513_);
lean_dec_ref(v_x_3512_);
v_r_3515_ = lean_box(v_res_3514_);
return v_r_3515_;
}
}
LEAN_EXPORT uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object* v_x_3518_, lean_object* v_x_3519_){
_start:
{
lean_object* v_sec_3520_; uint32_t v_nsec_3521_; lean_object* v_sec_3522_; uint32_t v_nsec_3523_; uint8_t v___x_3524_; 
v_sec_3520_ = lean_ctor_get(v_x_3518_, 0);
v_nsec_3521_ = lean_ctor_get_uint32(v_x_3518_, sizeof(void*)*1);
v_sec_3522_ = lean_ctor_get(v_x_3519_, 0);
v_nsec_3523_ = lean_ctor_get_uint32(v_x_3519_, sizeof(void*)*1);
v___x_3524_ = lean_int_dec_lt(v_sec_3520_, v_sec_3522_);
if (v___x_3524_ == 0)
{
uint8_t v___x_3525_; 
v___x_3525_ = lean_int_dec_eq(v_sec_3520_, v_sec_3522_);
if (v___x_3525_ == 0)
{
uint8_t v___x_3526_; 
v___x_3526_ = 2;
return v___x_3526_;
}
else
{
uint8_t v___x_3527_; 
v___x_3527_ = lean_uint32_dec_lt(v_nsec_3521_, v_nsec_3523_);
if (v___x_3527_ == 0)
{
uint8_t v___x_3528_; 
v___x_3528_ = lean_uint32_dec_eq(v_nsec_3521_, v_nsec_3523_);
if (v___x_3528_ == 0)
{
uint8_t v___x_3529_; 
v___x_3529_ = 2;
return v___x_3529_;
}
else
{
uint8_t v___x_3530_; 
v___x_3530_ = 1;
return v___x_3530_;
}
}
else
{
uint8_t v___x_3531_; 
v___x_3531_ = 0;
return v___x_3531_;
}
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
LEAN_EXPORT lean_object* l_IO_FS_instOrdSystemTime_ord___boxed(lean_object* v_x_3533_, lean_object* v_x_3534_){
_start:
{
uint8_t v_res_3535_; lean_object* v_r_3536_; 
v_res_3535_ = l_IO_FS_instOrdSystemTime_ord(v_x_3533_, v_x_3534_);
lean_dec_ref(v_x_3534_);
lean_dec_ref(v_x_3533_);
v_r_3536_ = lean_box(v_res_3535_);
return v_r_3536_;
}
}
static uint32_t _init_l_IO_FS_instInhabitedSystemTime_default___closed__0(void){
_start:
{
lean_object* v___x_3539_; uint32_t v___x_3540_; 
v___x_3539_ = lean_unsigned_to_nat(0u);
v___x_3540_ = lean_uint32_of_nat(v___x_3539_);
return v___x_3540_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default___closed__1(void){
_start:
{
uint32_t v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_uint32_once(&l_IO_FS_instInhabitedSystemTime_default___closed__0, &l_IO_FS_instInhabitedSystemTime_default___closed__0_once, _init_l_IO_FS_instInhabitedSystemTime_default___closed__0);
v___x_3542_ = lean_obj_once(&l_IO_FS_instReprSystemTime_repr___redArg___closed__7, &l_IO_FS_instReprSystemTime_repr___redArg___closed__7_once, _init_l_IO_FS_instReprSystemTime_repr___redArg___closed__7);
v___x_3543_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
lean_ctor_set_uint32(v___x_3543_, sizeof(void*)*1, v___x_3541_);
return v___x_3543_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime_default(void){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = lean_obj_once(&l_IO_FS_instInhabitedSystemTime_default___closed__1, &l_IO_FS_instInhabitedSystemTime_default___closed__1_once, _init_l_IO_FS_instInhabitedSystemTime_default___closed__1);
return v___x_3544_;
}
}
static lean_object* _init_l_IO_FS_instInhabitedSystemTime(void){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_IO_FS_instInhabitedSystemTime_default;
return v___x_3545_;
}
}
static lean_object* _init_l_IO_FS_instLTSystemTime(void){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_box(0);
return v___x_3546_;
}
}
static lean_object* _init_l_IO_FS_instLESystemTime(void){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = lean_box(0);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg(lean_object* v_x_3569_){
_start:
{
lean_object* v_accessed_3570_; lean_object* v_modified_3571_; uint64_t v_byteSize_3572_; uint8_t v_type_3573_; uint64_t v_numLinks_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v_accessed_3570_ = lean_ctor_get(v_x_3569_, 0);
v_modified_3571_ = lean_ctor_get(v_x_3569_, 1);
v_byteSize_3572_ = lean_ctor_get_uint64(v_x_3569_, sizeof(void*)*2);
v_type_3573_ = lean_ctor_get_uint8(v_x_3569_, sizeof(void*)*2 + 16);
v_numLinks_3574_ = lean_ctor_get_uint64(v_x_3569_, sizeof(void*)*2 + 8);
v___x_3575_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__5));
v___x_3576_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__3));
v___x_3577_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__14, &l_IO_FS_instReprDirEntry_repr___redArg___closed__14_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__14);
v___x_3578_ = lean_unsigned_to_nat(0u);
v___x_3579_ = l_IO_FS_instReprSystemTime_repr___redArg(v_accessed_3570_);
v___x_3580_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3577_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
v___x_3581_ = 0;
v___x_3582_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3582_, 0, v___x_3580_);
lean_ctor_set_uint8(v___x_3582_, sizeof(void*)*1, v___x_3581_);
v___x_3583_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3576_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
v___x_3584_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__11));
v___x_3585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3583_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = lean_box(1);
v___x_3587_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3585_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
v___x_3588_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__5));
v___x_3589_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3587_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
lean_ctor_set(v___x_3590_, 1, v___x_3575_);
v___x_3591_ = l_IO_FS_instReprSystemTime_repr___redArg(v_modified_3571_);
v___x_3592_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3577_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
v___x_3593_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
lean_ctor_set_uint8(v___x_3593_, sizeof(void*)*1, v___x_3581_);
v___x_3594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3590_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
v___x_3595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
lean_ctor_set(v___x_3595_, 1, v___x_3584_);
v___x_3596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
lean_ctor_set(v___x_3596_, 1, v___x_3586_);
v___x_3597_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__7));
v___x_3598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3596_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
lean_ctor_set(v___x_3599_, 1, v___x_3575_);
v___x_3600_ = lean_uint64_to_nat(v_byteSize_3572_);
v___x_3601_ = l_Nat_reprFast(v___x_3600_);
v___x_3602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
v___x_3603_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3577_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3604_, 0, v___x_3603_);
lean_ctor_set_uint8(v___x_3604_, sizeof(void*)*1, v___x_3581_);
v___x_3605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3599_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
lean_ctor_set(v___x_3606_, 1, v___x_3584_);
v___x_3607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
lean_ctor_set(v___x_3607_, 1, v___x_3586_);
v___x_3608_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__9));
v___x_3609_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3607_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
lean_ctor_set(v___x_3610_, 1, v___x_3575_);
v___x_3611_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__7, &l_IO_FS_instReprDirEntry_repr___redArg___closed__7_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__7);
v___x_3612_ = l_IO_FS_instReprFileType_repr(v_type_3573_, v___x_3578_);
v___x_3613_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3611_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
lean_ctor_set_uint8(v___x_3614_, sizeof(void*)*1, v___x_3581_);
v___x_3615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3610_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
lean_ctor_set(v___x_3616_, 1, v___x_3584_);
v___x_3617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
lean_ctor_set(v___x_3617_, 1, v___x_3586_);
v___x_3618_ = ((lean_object*)(l_IO_FS_instReprMetadata_repr___redArg___closed__11));
v___x_3619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3617_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
lean_ctor_set(v___x_3620_, 1, v___x_3575_);
v___x_3621_ = lean_uint64_to_nat(v_numLinks_3574_);
v___x_3622_ = l_Nat_reprFast(v___x_3621_);
v___x_3623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
v___x_3624_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3577_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
lean_ctor_set_uint8(v___x_3625_, sizeof(void*)*1, v___x_3581_);
v___x_3626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3620_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = lean_obj_once(&l_IO_FS_instReprDirEntry_repr___redArg___closed__17, &l_IO_FS_instReprDirEntry_repr___redArg___closed__17_once, _init_l_IO_FS_instReprDirEntry_repr___redArg___closed__17);
v___x_3628_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__18));
v___x_3629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
lean_ctor_set(v___x_3629_, 1, v___x_3626_);
v___x_3630_ = ((lean_object*)(l_IO_FS_instReprDirEntry_repr___redArg___closed__19));
v___x_3631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3629_);
lean_ctor_set(v___x_3631_, 1, v___x_3630_);
v___x_3632_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3627_);
lean_ctor_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
lean_ctor_set_uint8(v___x_3633_, sizeof(void*)*1, v___x_3581_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___redArg___boxed(lean_object* v_x_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_3634_);
lean_dec_ref(v_x_3634_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr(lean_object* v_x_3636_, lean_object* v_prec_3637_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l_IO_FS_instReprMetadata_repr___redArg(v_x_3636_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_instReprMetadata_repr___boxed(lean_object* v_x_3639_, lean_object* v_prec_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_IO_FS_instReprMetadata_repr(v_x_3639_, v_prec_3640_);
lean_dec(v_prec_3640_);
lean_dec_ref(v_x_3639_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_readDir___boxed(lean_object* v_a_00___x40___internal___hyg_3646_, lean_object* v_a_00___x40___internal___hyg_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = lean_io_read_dir(v_a_00___x40___internal___hyg_3646_);
lean_dec_ref(v_a_00___x40___internal___hyg_3646_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_metadata___boxed(lean_object* v_a_00___x40___internal___hyg_3651_, lean_object* v_a_00___x40___internal___hyg_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = lean_io_metadata(v_a_00___x40___internal___hyg_3651_);
lean_dec_ref(v_a_00___x40___internal___hyg_3651_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_symlinkMetadata___boxed(lean_object* v_a_00___x40___internal___hyg_3656_, lean_object* v_a_00___x40___internal___hyg_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = lean_io_symlink_metadata(v_a_00___x40___internal___hyg_3656_);
lean_dec_ref(v_a_00___x40___internal___hyg_3656_);
return v_res_3658_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isDir(lean_object* v_p_3659_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = lean_io_metadata(v_p_3659_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; uint8_t v_type_3663_; uint8_t v___x_3664_; uint8_t v___x_3665_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3661_, 1);
v_type_3663_ = lean_ctor_get_uint8(v_a_3662_, sizeof(void*)*2 + 16);
lean_dec(v_a_3662_);
v___x_3664_ = 0;
v___x_3665_ = l_IO_FS_instBEqFileType_beq(v_type_3663_, v___x_3664_);
return v___x_3665_;
}
else
{
uint8_t v___x_3666_; 
lean_dec_ref_known(v___x_3661_, 1);
v___x_3666_ = 0;
return v___x_3666_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isDir___boxed(lean_object* v_p_3667_, lean_object* v_a_3668_){
_start:
{
uint8_t v_res_3669_; lean_object* v_r_3670_; 
v_res_3669_ = l_System_FilePath_isDir(v_p_3667_);
lean_dec_ref(v_p_3667_);
v_r_3670_ = lean_box(v_res_3669_);
return v_r_3670_;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_pathExists(lean_object* v_p_3671_){
_start:
{
lean_object* v___x_3673_; 
v___x_3673_ = lean_io_metadata(v_p_3671_);
if (lean_obj_tag(v___x_3673_) == 0)
{
uint8_t v___x_3674_; 
lean_dec_ref_known(v___x_3673_, 1);
v___x_3674_ = 1;
return v___x_3674_;
}
else
{
uint8_t v___x_3675_; 
lean_dec_ref_known(v___x_3673_, 1);
v___x_3675_ = 0;
return v___x_3675_;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_pathExists___boxed(lean_object* v_p_3676_, lean_object* v_a_3677_){
_start:
{
uint8_t v_res_3678_; lean_object* v_r_3679_; 
v_res_3678_ = l_System_FilePath_pathExists(v_p_3676_);
lean_dec_ref(v_p_3676_);
v_r_3679_ = lean_box(v_res_3678_);
return v_r_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(lean_object* v_enter_3680_, lean_object* v_p_3681_, lean_object* v_as_3682_, size_t v_sz_3683_, size_t v_i_3684_, lean_object* v_b_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_a_3689_; lean_object* v_snd_3690_; uint8_t v___x_3694_; 
v___x_3694_ = lean_usize_dec_lt(v_i_3684_, v_sz_3683_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
lean_dec_ref(v_p_3681_);
lean_dec_ref(v_enter_3680_);
v___x_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3695_, 0, v_b_3685_);
lean_ctor_set(v___x_3695_, 1, v___y_3686_);
v___x_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3695_);
return v___x_3696_;
}
else
{
lean_object* v___x_3697_; lean_object* v_a_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3697_ = lean_box(0);
v_a_3698_ = lean_array_uget_borrowed(v_as_3682_, v_i_3684_);
lean_inc(v_a_3698_);
v___x_3699_ = l_IO_FS_DirEntry_path(v_a_3698_);
lean_inc_ref(v___x_3699_);
v___x_3700_ = lean_array_push(v___y_3686_, v___x_3699_);
v___x_3701_ = lean_io_metadata(v___x_3699_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; uint8_t v_type_3703_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
lean_dec_ref_known(v___x_3701_, 1);
v_type_3703_ = lean_ctor_get_uint8(v_a_3702_, sizeof(void*)*2 + 16);
lean_dec(v_a_3702_);
switch(v_type_3703_)
{
case 2:
{
lean_object* v___x_3704_; 
v___x_3704_ = lean_io_realpath(v___x_3699_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; uint8_t v___x_3706_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3704_, 1);
v___x_3706_ = l_System_FilePath_isDir(v_a_3705_);
if (v___x_3706_ == 0)
{
lean_dec(v_a_3705_);
v_a_3689_ = v___x_3697_;
v_snd_3690_ = v___x_3700_;
goto v___jp_3688_;
}
else
{
lean_object* v___x_3707_; 
lean_inc_ref(v_enter_3680_);
lean_inc_ref(v_p_3681_);
v___x_3707_ = lean_apply_2(v_enter_3680_, v_p_3681_, lean_box(0));
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; uint8_t v___x_3709_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___x_3707_, 1);
v___x_3709_ = lean_unbox(v_a_3708_);
lean_dec(v_a_3708_);
if (v___x_3709_ == 0)
{
lean_dec(v_a_3705_);
v_a_3689_ = v___x_3697_;
v_snd_3690_ = v___x_3700_;
goto v___jp_3688_;
}
else
{
lean_object* v___x_3710_; 
lean_inc_ref(v_enter_3680_);
v___x_3710_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3680_, v_a_3705_, v___x_3700_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v_snd_3712_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3710_, 1);
v_snd_3712_ = lean_ctor_get(v_a_3711_, 1);
lean_inc(v_snd_3712_);
lean_dec(v_a_3711_);
v_a_3689_ = v___x_3697_;
v_snd_3690_ = v_snd_3712_;
goto v___jp_3688_;
}
else
{
lean_dec_ref(v_p_3681_);
lean_dec_ref(v_enter_3680_);
return v___x_3710_;
}
}
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_dec(v_a_3705_);
lean_dec_ref(v___x_3700_);
lean_dec_ref(v_p_3681_);
lean_dec_ref(v_enter_3680_);
v_a_3713_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3707_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3707_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_dec_ref(v___x_3700_);
lean_dec_ref(v_p_3681_);
lean_dec_ref(v_enter_3680_);
v_a_3721_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3704_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3704_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
case 0:
{
lean_object* v___x_3729_; 
lean_inc_ref(v_enter_3680_);
v___x_3729_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3680_, v___x_3699_, v___x_3700_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v_snd_3731_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3729_, 1);
v_snd_3731_ = lean_ctor_get(v_a_3730_, 1);
lean_inc(v_snd_3731_);
lean_dec(v_a_3730_);
v_a_3689_ = v___x_3697_;
v_snd_3690_ = v_snd_3731_;
goto v___jp_3688_;
}
else
{
lean_dec_ref(v_p_3681_);
lean_dec_ref(v_enter_3680_);
return v___x_3729_;
}
}
default: 
{
lean_dec_ref(v___x_3699_);
v_a_3689_ = v___x_3697_;
v_snd_3690_ = v___x_3700_;
goto v___jp_3688_;
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec_ref(v___x_3699_);
v_a_3732_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3701_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3701_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
if (lean_obj_tag(v_a_3732_) == 11)
{
lean_dec_ref_known(v_a_3732_, 2);
lean_del_object(v___x_3734_);
v_a_3689_ = v___x_3697_;
v_snd_3690_ = v___x_3700_;
goto v___jp_3688_;
}
else
{
lean_object* v___x_3737_; 
lean_dec_ref(v___x_3700_);
lean_dec_ref(v_p_3681_);
lean_dec_ref(v_enter_3680_);
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
}
v___jp_3688_:
{
size_t v___x_3691_; size_t v___x_3692_; 
v___x_3691_ = ((size_t)1ULL);
v___x_3692_ = lean_usize_add(v_i_3684_, v___x_3691_);
v_i_3684_ = v___x_3692_;
v_b_3685_ = v_a_3689_;
v___y_3686_ = v_snd_3690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go(lean_object* v_enter_3740_, lean_object* v_p_3741_, lean_object* v_a_3742_){
_start:
{
lean_object* v___x_3744_; 
lean_inc_ref(v_enter_3740_);
lean_inc_ref(v_p_3741_);
v___x_3744_ = lean_apply_2(v_enter_3740_, v_p_3741_, lean_box(0));
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3786_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3747_ = v___x_3744_;
v_isShared_3748_ = v_isSharedCheck_3786_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3744_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3786_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
uint8_t v___x_3749_; 
v___x_3749_ = lean_unbox(v_a_3745_);
lean_dec(v_a_3745_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3753_; 
lean_dec_ref(v_p_3741_);
lean_dec_ref(v_enter_3740_);
v___x_3750_ = lean_box(0);
v___x_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
lean_ctor_set(v___x_3751_, 1, v_a_3742_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v___x_3751_);
v___x_3753_ = v___x_3747_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3751_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
else
{
lean_object* v___x_3755_; 
lean_del_object(v___x_3747_);
v___x_3755_ = lean_io_read_dir(v_p_3741_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3757_; size_t v_sz_3758_; size_t v___x_3759_; lean_object* v___x_3760_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3755_, 1);
v___x_3757_ = lean_box(0);
v_sz_3758_ = lean_array_size(v_a_3756_);
v___x_3759_ = ((size_t)0ULL);
v___x_3760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_3740_, v_p_3741_, v_a_3756_, v_sz_3758_, v___x_3759_, v___x_3757_, v_a_3742_);
lean_dec(v_a_3756_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3777_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3777_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3777_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v_snd_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3775_; 
v_snd_3765_ = lean_ctor_get(v_a_3761_, 1);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_a_3761_);
if (v_isSharedCheck_3775_ == 0)
{
lean_object* v_unused_3776_; 
v_unused_3776_ = lean_ctor_get(v_a_3761_, 0);
lean_dec(v_unused_3776_);
v___x_3767_ = v_a_3761_;
v_isShared_3768_ = v_isSharedCheck_3775_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_snd_3765_);
lean_dec(v_a_3761_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3775_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 0, v___x_3757_);
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_snd_3765_);
v___x_3770_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
lean_object* v___x_3772_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3770_);
v___x_3772_ = v___x_3763_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
}
else
{
return v___x_3760_;
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
lean_dec_ref(v_a_3742_);
lean_dec_ref(v_p_3741_);
lean_dec_ref(v_enter_3740_);
v_a_3778_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3755_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3755_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec_ref(v_a_3742_);
lean_dec_ref(v_p_3741_);
lean_dec_ref(v_enter_3740_);
v_a_3787_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3744_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3744_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__System_FilePath_walkDir_go___boxed(lean_object* v_enter_3795_, lean_object* v_p_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3795_, v_p_3796_, v_a_3797_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0___boxed(lean_object* v_enter_3800_, lean_object* v_p_3801_, lean_object* v_as_3802_, lean_object* v_sz_3803_, lean_object* v_i_3804_, lean_object* v_b_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
size_t v_sz_boxed_3808_; size_t v_i_boxed_3809_; lean_object* v_res_3810_; 
v_sz_boxed_3808_ = lean_unbox_usize(v_sz_3803_);
lean_dec(v_sz_3803_);
v_i_boxed_3809_ = lean_unbox_usize(v_i_3804_);
lean_dec(v_i_3804_);
v_res_3810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_System_IO_0__System_FilePath_walkDir_go_spec__0(v_enter_3800_, v_p_3801_, v_as_3802_, v_sz_boxed_3808_, v_i_boxed_3809_, v_b_3805_, v___y_3806_);
lean_dec_ref(v_as_3802_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir(lean_object* v_p_3811_, lean_object* v_enter_3812_){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_3815_ = l___private_Init_System_IO_0__System_FilePath_walkDir_go(v_enter_3812_, v_p_3811_, v___x_3814_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3824_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3818_ = v___x_3815_;
v_isShared_3819_ = v_isSharedCheck_3824_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3815_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3824_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v_snd_3820_; lean_object* v___x_3822_; 
v_snd_3820_ = lean_ctor_get(v_a_3816_, 1);
lean_inc(v_snd_3820_);
lean_dec(v_a_3816_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v_snd_3820_);
v___x_3822_ = v___x_3818_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_snd_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v_a_3825_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3815_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3815_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_walkDir___boxed(lean_object* v_p_3833_, lean_object* v_enter_3834_, lean_object* v_a_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_System_FilePath_walkDir(v_p_3833_, v_enter_3834_);
return v_res_3836_;
}
}
static lean_object* _init_l_IO_FS_readBinFile___closed__0(void){
_start:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3837_ = lean_unsigned_to_nat(0u);
v___x_3838_ = lean_mk_empty_byte_array(v___x_3837_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile(lean_object* v_fname_3839_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_io_metadata(v_fname_3839_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_a_3842_; uint8_t v___x_3843_; lean_object* v___x_3844_; 
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc(v_a_3842_);
lean_dec_ref_known(v___x_3841_, 1);
v___x_3843_ = 0;
v___x_3844_ = lean_io_prim_handle_mk(v_fname_3839_, v___x_3843_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; uint64_t v_byteSize_3846_; size_t v___x_3847_; size_t v___x_3848_; uint8_t v___x_3849_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref_known(v___x_3844_, 1);
v_byteSize_3846_ = lean_ctor_get_uint64(v_a_3842_, sizeof(void*)*2);
lean_dec(v_a_3842_);
v___x_3847_ = lean_uint64_to_usize(v_byteSize_3846_);
v___x_3848_ = ((size_t)0ULL);
v___x_3849_ = lean_usize_dec_lt(v___x_3848_, v___x_3847_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3850_ = lean_obj_once(&l_IO_FS_readBinFile___closed__0, &l_IO_FS_readBinFile___closed__0_once, _init_l_IO_FS_readBinFile___closed__0);
v___x_3851_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_a_3845_, v___x_3850_);
lean_dec(v_a_3845_);
return v___x_3851_;
}
else
{
lean_object* v___x_3852_; 
v___x_3852_ = lean_io_prim_handle_read(v_a_3845_, v___x_3847_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3854_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3852_, 1);
v___x_3854_ = l___private_Init_System_IO_0__IO_FS_Handle_readBinToEndInto_loop(v_a_3845_, v_a_3853_);
lean_dec(v_a_3845_);
return v___x_3854_;
}
else
{
lean_dec(v_a_3845_);
return v___x_3852_;
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec(v_a_3842_);
v_a_3855_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3844_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3844_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
v_a_3863_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3841_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3841_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readBinFile___boxed(lean_object* v_fname_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_IO_FS_readBinFile(v_fname_3871_);
lean_dec_ref(v_fname_3871_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile(lean_object* v_fname_3876_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l_IO_FS_readBinFile(v_fname_3876_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3896_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3881_ = v___x_3878_;
v_isShared_3882_ = v_isSharedCheck_3896_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3896_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
uint8_t v___x_3883_; 
v___x_3883_ = lean_string_validate_utf8(v_a_3879_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3890_; 
lean_dec(v_a_3879_);
v___x_3884_ = ((lean_object*)(l_IO_FS_readFile___closed__0));
v___x_3885_ = lean_string_append(v___x_3884_, v_fname_3876_);
v___x_3886_ = ((lean_object*)(l_IO_FS_readFile___closed__1));
v___x_3887_ = lean_string_append(v___x_3885_, v___x_3886_);
v___x_3888_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set_tag(v___x_3881_, 1);
lean_ctor_set(v___x_3881_, 0, v___x_3888_);
v___x_3890_ = v___x_3881_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3888_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
else
{
lean_object* v___x_3892_; lean_object* v___x_3894_; 
v___x_3892_ = lean_string_from_utf8_unchecked(v_a_3879_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 0, v___x_3892_);
v___x_3894_ = v___x_3881_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3892_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
v_a_3897_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3878_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3878_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_readFile___boxed(lean_object* v_fname_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_IO_FS_readFile(v_fname_3905_);
lean_dec_ref(v_fname_3905_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0(lean_object* v_x_3908_){
_start:
{
lean_object* v_fst_3909_; 
v_fst_3909_ = lean_ctor_get(v_x_3908_, 0);
lean_inc(v_fst_3909_);
return v_fst_3909_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__0___boxed(lean_object* v_x_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_IO_withStdin___redArg___lam__0(v_x_3910_);
lean_dec_ref(v_x_3910_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1(lean_object* v___x_3912_, lean_object* v_x_3913_){
_start:
{
lean_inc(v___x_3912_);
return v___x_3912_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__1___boxed(lean_object* v___x_3914_, lean_object* v_x_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l_IO_withStdin___redArg___lam__1(v___x_3914_, v_x_3915_);
lean_dec(v_x_3915_);
lean_dec(v___x_3914_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg___lam__2(lean_object* v_toFunctor_3917_, lean_object* v_inst_3918_, lean_object* v_inst_3919_, lean_object* v_x_3920_, lean_object* v___f_3921_, lean_object* v_prev_3922_){
_start:
{
lean_object* v_map_3923_; lean_object* v_mapConst_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___f_3929_; lean_object* v_y_3930_; lean_object* v___x_3931_; 
v_map_3923_ = lean_ctor_get(v_toFunctor_3917_, 0);
lean_inc(v_map_3923_);
v_mapConst_3924_ = lean_ctor_get(v_toFunctor_3917_, 1);
lean_inc(v_mapConst_3924_);
lean_dec_ref(v_toFunctor_3917_);
v___x_3925_ = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(v___x_3925_, 0, v_prev_3922_);
v___x_3926_ = lean_apply_2(v_inst_3918_, lean_box(0), v___x_3925_);
v___x_3927_ = lean_box(0);
v___x_3928_ = lean_apply_4(v_mapConst_3924_, lean_box(0), lean_box(0), v___x_3927_, v___x_3926_);
v___f_3929_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3929_, 0, v___x_3928_);
v_y_3930_ = lean_apply_4(v_inst_3919_, lean_box(0), lean_box(0), v_x_3920_, v___f_3929_);
v___x_3931_ = lean_apply_4(v_map_3923_, lean_box(0), lean_box(0), v___f_3921_, v_y_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___redArg(lean_object* v_inst_3933_, lean_object* v_inst_3934_, lean_object* v_inst_3935_, lean_object* v_h_3936_, lean_object* v_x_3937_){
_start:
{
lean_object* v_toApplicative_3938_; lean_object* v_toBind_3939_; lean_object* v_toFunctor_3940_; lean_object* v___f_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___f_3944_; lean_object* v___x_3945_; 
v_toApplicative_3938_ = lean_ctor_get(v_inst_3933_, 0);
lean_inc_ref(v_toApplicative_3938_);
v_toBind_3939_ = lean_ctor_get(v_inst_3933_, 1);
lean_inc(v_toBind_3939_);
lean_dec_ref(v_inst_3933_);
v_toFunctor_3940_ = lean_ctor_get(v_toApplicative_3938_, 0);
lean_inc_ref(v_toFunctor_3940_);
lean_dec_ref(v_toApplicative_3938_);
v___f_3941_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3942_ = lean_alloc_closure((void*)(l_IO_setStdin___boxed), 2, 1);
lean_closure_set(v___x_3942_, 0, v_h_3936_);
lean_inc(v_inst_3935_);
v___x_3943_ = lean_apply_2(v_inst_3935_, lean_box(0), v___x_3942_);
v___f_3944_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3944_, 0, v_toFunctor_3940_);
lean_closure_set(v___f_3944_, 1, v_inst_3935_);
lean_closure_set(v___f_3944_, 2, v_inst_3934_);
lean_closure_set(v___f_3944_, 3, v_x_3937_);
lean_closure_set(v___f_3944_, 4, v___f_3941_);
v___x_3945_ = lean_apply_4(v_toBind_3939_, lean_box(0), lean_box(0), v___x_3943_, v___f_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin(lean_object* v_m_3946_, lean_object* v_00_u03b1_3947_, lean_object* v_inst_3948_, lean_object* v_inst_3949_, lean_object* v_inst_3950_, lean_object* v_h_3951_, lean_object* v_x_3952_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l_IO_withStdin___redArg(v_inst_3948_, v_inst_3949_, v_inst_3950_, v_h_3951_, v_x_3952_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg___lam__2(lean_object* v_toFunctor_3954_, lean_object* v_inst_3955_, lean_object* v_inst_3956_, lean_object* v_x_3957_, lean_object* v___f_3958_, lean_object* v_prev_3959_){
_start:
{
lean_object* v_map_3960_; lean_object* v_mapConst_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___f_3966_; lean_object* v_y_3967_; lean_object* v___x_3968_; 
v_map_3960_ = lean_ctor_get(v_toFunctor_3954_, 0);
lean_inc(v_map_3960_);
v_mapConst_3961_ = lean_ctor_get(v_toFunctor_3954_, 1);
lean_inc(v_mapConst_3961_);
lean_dec_ref(v_toFunctor_3954_);
v___x_3962_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_3962_, 0, v_prev_3959_);
v___x_3963_ = lean_apply_2(v_inst_3955_, lean_box(0), v___x_3962_);
v___x_3964_ = lean_box(0);
v___x_3965_ = lean_apply_4(v_mapConst_3961_, lean_box(0), lean_box(0), v___x_3964_, v___x_3963_);
v___f_3966_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3966_, 0, v___x_3965_);
v_y_3967_ = lean_apply_4(v_inst_3956_, lean_box(0), lean_box(0), v_x_3957_, v___f_3966_);
v___x_3968_ = lean_apply_4(v_map_3960_, lean_box(0), lean_box(0), v___f_3958_, v_y_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___redArg(lean_object* v_inst_3969_, lean_object* v_inst_3970_, lean_object* v_inst_3971_, lean_object* v_h_3972_, lean_object* v_x_3973_){
_start:
{
lean_object* v_toApplicative_3974_; lean_object* v_toBind_3975_; lean_object* v_toFunctor_3976_; lean_object* v___f_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___f_3980_; lean_object* v___x_3981_; 
v_toApplicative_3974_ = lean_ctor_get(v_inst_3969_, 0);
lean_inc_ref(v_toApplicative_3974_);
v_toBind_3975_ = lean_ctor_get(v_inst_3969_, 1);
lean_inc(v_toBind_3975_);
lean_dec_ref(v_inst_3969_);
v_toFunctor_3976_ = lean_ctor_get(v_toApplicative_3974_, 0);
lean_inc_ref(v_toFunctor_3976_);
lean_dec_ref(v_toApplicative_3974_);
v___f_3977_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_3978_ = lean_alloc_closure((void*)(l_IO_setStdout___boxed), 2, 1);
lean_closure_set(v___x_3978_, 0, v_h_3972_);
lean_inc(v_inst_3971_);
v___x_3979_ = lean_apply_2(v_inst_3971_, lean_box(0), v___x_3978_);
v___f_3980_ = lean_alloc_closure((void*)(l_IO_withStdout___redArg___lam__2), 6, 5);
lean_closure_set(v___f_3980_, 0, v_toFunctor_3976_);
lean_closure_set(v___f_3980_, 1, v_inst_3971_);
lean_closure_set(v___f_3980_, 2, v_inst_3970_);
lean_closure_set(v___f_3980_, 3, v_x_3973_);
lean_closure_set(v___f_3980_, 4, v___f_3977_);
v___x_3981_ = lean_apply_4(v_toBind_3975_, lean_box(0), lean_box(0), v___x_3979_, v___f_3980_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout(lean_object* v_m_3982_, lean_object* v_00_u03b1_3983_, lean_object* v_inst_3984_, lean_object* v_inst_3985_, lean_object* v_inst_3986_, lean_object* v_h_3987_, lean_object* v_x_3988_){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = l_IO_withStdout___redArg(v_inst_3984_, v_inst_3985_, v_inst_3986_, v_h_3987_, v_x_3988_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg___lam__2(lean_object* v_toFunctor_3990_, lean_object* v_inst_3991_, lean_object* v_inst_3992_, lean_object* v_x_3993_, lean_object* v___f_3994_, lean_object* v_prev_3995_){
_start:
{
lean_object* v_map_3996_; lean_object* v_mapConst_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___f_4002_; lean_object* v_y_4003_; lean_object* v___x_4004_; 
v_map_3996_ = lean_ctor_get(v_toFunctor_3990_, 0);
lean_inc(v_map_3996_);
v_mapConst_3997_ = lean_ctor_get(v_toFunctor_3990_, 1);
lean_inc(v_mapConst_3997_);
lean_dec_ref(v_toFunctor_3990_);
v___x_3998_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_3998_, 0, v_prev_3995_);
v___x_3999_ = lean_apply_2(v_inst_3991_, lean_box(0), v___x_3998_);
v___x_4000_ = lean_box(0);
v___x_4001_ = lean_apply_4(v_mapConst_3997_, lean_box(0), lean_box(0), v___x_4000_, v___x_3999_);
v___f_4002_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4002_, 0, v___x_4001_);
v_y_4003_ = lean_apply_4(v_inst_3992_, lean_box(0), lean_box(0), v_x_3993_, v___f_4002_);
v___x_4004_ = lean_apply_4(v_map_3996_, lean_box(0), lean_box(0), v___f_3994_, v_y_4003_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___redArg(lean_object* v_inst_4005_, lean_object* v_inst_4006_, lean_object* v_inst_4007_, lean_object* v_h_4008_, lean_object* v_x_4009_){
_start:
{
lean_object* v_toApplicative_4010_; lean_object* v_toBind_4011_; lean_object* v_toFunctor_4012_; lean_object* v___f_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___f_4016_; lean_object* v___x_4017_; 
v_toApplicative_4010_ = lean_ctor_get(v_inst_4005_, 0);
lean_inc_ref(v_toApplicative_4010_);
v_toBind_4011_ = lean_ctor_get(v_inst_4005_, 1);
lean_inc(v_toBind_4011_);
lean_dec_ref(v_inst_4005_);
v_toFunctor_4012_ = lean_ctor_get(v_toApplicative_4010_, 0);
lean_inc_ref(v_toFunctor_4012_);
lean_dec_ref(v_toApplicative_4010_);
v___f_4013_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4014_ = lean_alloc_closure((void*)(l_IO_setStderr___boxed), 2, 1);
lean_closure_set(v___x_4014_, 0, v_h_4008_);
lean_inc(v_inst_4007_);
v___x_4015_ = lean_apply_2(v_inst_4007_, lean_box(0), v___x_4014_);
v___f_4016_ = lean_alloc_closure((void*)(l_IO_withStderr___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4016_, 0, v_toFunctor_4012_);
lean_closure_set(v___f_4016_, 1, v_inst_4007_);
lean_closure_set(v___f_4016_, 2, v_inst_4006_);
lean_closure_set(v___f_4016_, 3, v_x_4009_);
lean_closure_set(v___f_4016_, 4, v___f_4013_);
v___x_4017_ = lean_apply_4(v_toBind_4011_, lean_box(0), lean_box(0), v___x_4015_, v___f_4016_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr(lean_object* v_m_4018_, lean_object* v_00_u03b1_4019_, lean_object* v_inst_4020_, lean_object* v_inst_4021_, lean_object* v_inst_4022_, lean_object* v_h_4023_, lean_object* v_x_4024_){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = l_IO_withStderr___redArg(v_inst_4020_, v_inst_4021_, v_inst_4022_, v_h_4023_, v_x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_IO_print___redArg(lean_object* v_inst_4026_, lean_object* v_s_4027_){
_start:
{
lean_object* v___x_4029_; lean_object* v_putStr_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4029_ = lean_get_stdout();
v_putStr_4030_ = lean_ctor_get(v___x_4029_, 4);
lean_inc_ref(v_putStr_4030_);
lean_dec_ref(v___x_4029_);
v___x_4031_ = lean_apply_1(v_inst_4026_, v_s_4027_);
v___x_4032_ = lean_apply_2(v_putStr_4030_, v___x_4031_, lean_box(0));
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_IO_print___redArg___boxed(lean_object* v_inst_4033_, lean_object* v_s_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_IO_print___redArg(v_inst_4033_, v_s_4034_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_IO_print(lean_object* v_00_u03b1_4037_, lean_object* v_inst_4038_, lean_object* v_s_4039_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_IO_print___redArg(v_inst_4038_, v_s_4039_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_IO_print___boxed(lean_object* v_00_u03b1_4042_, lean_object* v_inst_4043_, lean_object* v_s_4044_, lean_object* v_a_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_IO_print(v_00_u03b1_4042_, v_inst_4043_, v_s_4044_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l_IO_println___redArg(lean_object* v_inst_4048_, lean_object* v_s_4049_){
_start:
{
lean_object* v___f_4051_; lean_object* v___x_4052_; uint32_t v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___f_4051_ = ((lean_object*)(l_IO_println___redArg___closed__0));
v___x_4052_ = lean_apply_1(v_inst_4048_, v_s_4049_);
v___x_4053_ = 10;
v___x_4054_ = lean_string_push(v___x_4052_, v___x_4053_);
v___x_4055_ = l_IO_print___redArg(v___f_4051_, v___x_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_IO_println___redArg___boxed(lean_object* v_inst_4056_, lean_object* v_s_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l_IO_println___redArg(v_inst_4056_, v_s_4057_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l_IO_println(lean_object* v_00_u03b1_4060_, lean_object* v_inst_4061_, lean_object* v_s_4062_){
_start:
{
lean_object* v___x_4064_; 
v___x_4064_ = l_IO_println___redArg(v_inst_4061_, v_s_4062_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_IO_println___boxed(lean_object* v_00_u03b1_4065_, lean_object* v_inst_4066_, lean_object* v_s_4067_, lean_object* v_a_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_IO_println(v_00_u03b1_4065_, v_inst_4066_, v_s_4067_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg(lean_object* v_inst_4070_, lean_object* v_s_4071_){
_start:
{
lean_object* v___x_4073_; lean_object* v_putStr_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4073_ = lean_get_stderr();
v_putStr_4074_ = lean_ctor_get(v___x_4073_, 4);
lean_inc_ref(v_putStr_4074_);
lean_dec_ref(v___x_4073_);
v___x_4075_ = lean_apply_1(v_inst_4070_, v_s_4071_);
v___x_4076_ = lean_apply_2(v_putStr_4074_, v___x_4075_, lean_box(0));
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___redArg___boxed(lean_object* v_inst_4077_, lean_object* v_s_4078_, lean_object* v_a_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = l_IO_eprint___redArg(v_inst_4077_, v_s_4078_);
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint(lean_object* v_00_u03b1_4081_, lean_object* v_inst_4082_, lean_object* v_s_4083_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_IO_eprint___redArg(v_inst_4082_, v_s_4083_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___boxed(lean_object* v_00_u03b1_4086_, lean_object* v_inst_4087_, lean_object* v_s_4088_, lean_object* v_a_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_IO_eprint(v_00_u03b1_4086_, v_inst_4087_, v_s_4088_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg(lean_object* v_inst_4091_, lean_object* v_s_4092_){
_start:
{
lean_object* v___f_4094_; lean_object* v___x_4095_; uint32_t v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___f_4094_ = ((lean_object*)(l_IO_println___redArg___closed__0));
v___x_4095_ = lean_apply_1(v_inst_4091_, v_s_4092_);
v___x_4096_ = 10;
v___x_4097_ = lean_string_push(v___x_4095_, v___x_4096_);
v___x_4098_ = l_IO_eprint___redArg(v___f_4094_, v___x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___redArg___boxed(lean_object* v_inst_4099_, lean_object* v_s_4100_, lean_object* v_a_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_IO_eprintln___redArg(v_inst_4099_, v_s_4100_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln(lean_object* v_00_u03b1_4103_, lean_object* v_inst_4104_, lean_object* v_s_4105_){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l_IO_eprintln___redArg(v_inst_4104_, v_s_4105_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___boxed(lean_object* v_00_u03b1_4108_, lean_object* v_inst_4109_, lean_object* v_s_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_IO_eprintln(v_00_u03b1_4108_, v_inst_4109_, v_s_4110_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object* v_s_4113_){
_start:
{
lean_object* v___x_4115_; lean_object* v_putStr_4116_; lean_object* v___x_4117_; 
v___x_4115_ = lean_get_stderr();
v_putStr_4116_ = lean_ctor_get(v___x_4115_, 4);
lean_inc_ref(v_putStr_4116_);
lean_dec_ref(v___x_4115_);
v___x_4117_ = lean_apply_2(v_putStr_4116_, v_s_4113_, lean_box(0));
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0___boxed(lean_object* v_s_4118_, lean_object* v_a_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_4118_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* lean_io_eprint(lean_object* v_s_4121_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v_s_4121_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintAux___boxed(lean_object* v_s_4124_, lean_object* v_a_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = lean_io_eprint(v_s_4124_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object* v_s_4127_){
_start:
{
uint32_t v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4129_ = 10;
v___x_4130_ = lean_string_push(v_s_4127_, v___x_4129_);
v___x_4131_ = l_IO_eprint___at___00__private_Init_System_IO_0__IO_eprintAux_spec__0(v___x_4130_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0___boxed(lean_object* v_s_4132_, lean_object* v_a_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_4132_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* lean_io_eprintln(lean_object* v_s_4135_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v_s_4135_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_eprintlnAux___boxed(lean_object* v_s_4138_, lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = lean_io_eprintln(v_s_4138_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_IO_appDir(){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = lean_io_app_path();
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4160_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4147_ = v___x_4144_;
v_isShared_4148_ = v_isSharedCheck_4160_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4144_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4160_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4149_; 
lean_inc(v_a_4145_);
v___x_4149_ = l_System_FilePath_parent(v_a_4145_);
if (lean_obj_tag(v___x_4149_) == 1)
{
lean_object* v_val_4150_; lean_object* v___x_4151_; 
lean_del_object(v___x_4147_);
lean_dec(v_a_4145_);
v_val_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_val_4150_);
lean_dec_ref_known(v___x_4149_, 1);
v___x_4151_ = lean_io_realpath(v_val_4150_);
return v___x_4151_;
}
else
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4158_; 
lean_dec(v___x_4149_);
v___x_4152_ = ((lean_object*)(l_IO_appDir___closed__0));
v___x_4153_ = lean_string_append(v___x_4152_, v_a_4145_);
lean_dec(v_a_4145_);
v___x_4154_ = ((lean_object*)(l_IO_appDir___closed__1));
v___x_4155_ = lean_string_append(v___x_4153_, v___x_4154_);
v___x_4156_ = lean_mk_io_user_error(v___x_4155_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set_tag(v___x_4147_, 1);
lean_ctor_set(v___x_4147_, 0, v___x_4156_);
v___x_4158_ = v___x_4147_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___x_4156_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
else
{
return v___x_4144_;
}
}
}
LEAN_EXPORT lean_object* l_IO_appDir___boxed(lean_object* v_a_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l_IO_appDir();
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll(lean_object* v_p_4163_){
_start:
{
uint8_t v___x_4180_; 
v___x_4180_ = l_System_FilePath_isDir(v_p_4163_);
if (v___x_4180_ == 0)
{
lean_object* v___x_4181_; 
lean_inc_ref(v_p_4163_);
v___x_4181_ = l_System_FilePath_parent(v_p_4163_);
if (lean_obj_tag(v___x_4181_) == 1)
{
lean_object* v_val_4182_; lean_object* v___x_4183_; 
v_val_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_val_4182_);
lean_dec_ref_known(v___x_4181_, 1);
v___x_4183_ = l_IO_FS_createDirAll(v_val_4182_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_dec_ref_known(v___x_4183_, 1);
goto v___jp_4165_;
}
else
{
lean_dec_ref(v_p_4163_);
return v___x_4183_;
}
}
else
{
lean_dec(v___x_4181_);
goto v___jp_4165_;
}
}
else
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_dec_ref(v_p_4163_);
v___x_4184_ = lean_box(0);
v___x_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
return v___x_4185_;
}
v___jp_4165_:
{
lean_object* v___x_4166_; 
v___x_4166_ = lean_io_create_dir(v_p_4163_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_dec_ref(v_p_4163_);
return v___x_4166_;
}
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4179_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4169_ = v___x_4166_;
v_isShared_4170_ = v_isSharedCheck_4179_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4166_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4179_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
uint8_t v___x_4171_; 
v___x_4171_ = l_System_FilePath_isDir(v_p_4163_);
lean_dec_ref(v_p_4163_);
if (v___x_4171_ == 0)
{
lean_object* v___x_4173_; 
if (v_isShared_4170_ == 0)
{
v___x_4173_ = v___x_4169_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4167_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
else
{
lean_object* v___x_4175_; lean_object* v___x_4177_; 
lean_dec(v_a_4167_);
v___x_4175_ = lean_box(0);
if (v_isShared_4170_ == 0)
{
lean_ctor_set_tag(v___x_4169_, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4175_);
v___x_4177_ = v___x_4169_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4175_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_createDirAll___boxed(lean_object* v_p_4186_, lean_object* v_a_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_IO_FS_createDirAll(v_p_4186_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(lean_object* v_as_4189_, size_t v_sz_4190_, size_t v_i_4191_, lean_object* v_b_4192_){
_start:
{
lean_object* v_a_4195_; uint8_t v___x_4199_; 
v___x_4199_ = lean_usize_dec_lt(v_i_4191_, v_sz_4190_);
if (v___x_4199_ == 0)
{
lean_object* v___x_4200_; 
v___x_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4200_, 0, v_b_4192_);
return v___x_4200_;
}
else
{
lean_object* v_a_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v_a_4201_ = lean_array_uget_borrowed(v_as_4189_, v_i_4191_);
lean_inc(v_a_4201_);
v___x_4202_ = l_IO_FS_DirEntry_path(v_a_4201_);
v___x_4203_ = lean_io_symlink_metadata(v___x_4202_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; uint8_t v_type_4205_; lean_object* v___x_4206_; uint8_t v___x_4207_; uint8_t v___x_4208_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4203_, 1);
v_type_4205_ = lean_ctor_get_uint8(v_a_4204_, sizeof(void*)*2 + 16);
lean_dec(v_a_4204_);
v___x_4206_ = lean_box(0);
v___x_4207_ = 0;
v___x_4208_ = l_IO_FS_instBEqFileType_beq(v_type_4205_, v___x_4207_);
if (v___x_4208_ == 0)
{
lean_object* v___x_4209_; 
v___x_4209_ = lean_io_remove_file(v___x_4202_);
lean_dec_ref(v___x_4202_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_dec_ref_known(v___x_4209_, 1);
v_a_4195_ = v___x_4206_;
goto v___jp_4194_;
}
else
{
return v___x_4209_;
}
}
else
{
lean_object* v___x_4210_; 
v___x_4210_ = l_IO_FS_removeDirAll(v___x_4202_);
lean_dec_ref(v___x_4202_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_dec_ref_known(v___x_4210_, 1);
v_a_4195_ = v___x_4206_;
goto v___jp_4194_;
}
else
{
return v___x_4210_;
}
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
lean_dec_ref(v___x_4202_);
v_a_4211_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4203_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4203_);
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
v___jp_4194_:
{
size_t v___x_4196_; size_t v___x_4197_; 
v___x_4196_ = ((size_t)1ULL);
v___x_4197_ = lean_usize_add(v_i_4191_, v___x_4196_);
v_i_4191_ = v___x_4197_;
v_b_4192_ = v_a_4195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll(lean_object* v_p_4219_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = lean_io_read_dir(v_p_4219_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4223_; size_t v_sz_4224_; size_t v___x_4225_; lean_object* v___x_4226_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_a_4222_);
lean_dec_ref_known(v___x_4221_, 1);
v___x_4223_ = lean_box(0);
v_sz_4224_ = lean_array_size(v_a_4222_);
v___x_4225_ = ((size_t)0ULL);
v___x_4226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_a_4222_, v_sz_4224_, v___x_4225_, v___x_4223_);
lean_dec(v_a_4222_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v___x_4227_; 
lean_dec_ref_known(v___x_4226_, 1);
v___x_4227_ = lean_io_remove_dir(v_p_4219_);
return v___x_4227_;
}
else
{
return v___x_4226_;
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
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
}
LEAN_EXPORT lean_object* l_IO_FS_removeDirAll___boxed(lean_object* v_p_4236_, lean_object* v_a_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_IO_FS_removeDirAll(v_p_4236_);
lean_dec_ref(v_p_4236_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0___boxed(lean_object* v_as_4239_, lean_object* v_sz_4240_, lean_object* v_i_4241_, lean_object* v_b_4242_, lean_object* v___y_4243_){
_start:
{
size_t v_sz_boxed_4244_; size_t v_i_boxed_4245_; lean_object* v_res_4246_; 
v_sz_boxed_4244_ = lean_unbox_usize(v_sz_4240_);
lean_dec(v_sz_4240_);
v_i_boxed_4245_ = lean_unbox_usize(v_i_4241_);
lean_dec(v_i_4241_);
v_res_4246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00IO_FS_removeDirAll_spec__0(v_as_4239_, v_sz_boxed_4244_, v_i_boxed_4245_, v_b_4242_);
lean_dec_ref(v_as_4239_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg___lam__2(lean_object* v_toFunctor_4247_, lean_object* v_f_4248_, lean_object* v_inst_4249_, lean_object* v_inst_4250_, lean_object* v___f_4251_, lean_object* v_____x_4252_){
_start:
{
lean_object* v_fst_4253_; lean_object* v_snd_4254_; lean_object* v_map_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___f_4259_; lean_object* v_y_4260_; lean_object* v___x_4261_; 
v_fst_4253_ = lean_ctor_get(v_____x_4252_, 0);
lean_inc(v_fst_4253_);
v_snd_4254_ = lean_ctor_get(v_____x_4252_, 1);
lean_inc_n(v_snd_4254_, 2);
lean_dec_ref(v_____x_4252_);
v_map_4255_ = lean_ctor_get(v_toFunctor_4247_, 0);
lean_inc(v_map_4255_);
lean_dec_ref(v_toFunctor_4247_);
v___x_4256_ = lean_apply_2(v_f_4248_, v_fst_4253_, v_snd_4254_);
v___x_4257_ = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(v___x_4257_, 0, v_snd_4254_);
v___x_4258_ = lean_apply_2(v_inst_4249_, lean_box(0), v___x_4257_);
v___f_4259_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4259_, 0, v___x_4258_);
v_y_4260_ = lean_apply_4(v_inst_4250_, lean_box(0), lean_box(0), v___x_4256_, v___f_4259_);
v___x_4261_ = lean_apply_4(v_map_4255_, lean_box(0), lean_box(0), v___f_4251_, v_y_4260_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___redArg(lean_object* v_inst_4263_, lean_object* v_inst_4264_, lean_object* v_inst_4265_, lean_object* v_f_4266_){
_start:
{
lean_object* v_toApplicative_4267_; lean_object* v_toBind_4268_; lean_object* v_toFunctor_4269_; lean_object* v___f_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___f_4273_; lean_object* v___x_4274_; 
v_toApplicative_4267_ = lean_ctor_get(v_inst_4263_, 0);
lean_inc_ref(v_toApplicative_4267_);
v_toBind_4268_ = lean_ctor_get(v_inst_4263_, 1);
lean_inc(v_toBind_4268_);
lean_dec_ref(v_inst_4263_);
v_toFunctor_4269_ = lean_ctor_get(v_toApplicative_4267_, 0);
lean_inc_ref(v_toFunctor_4269_);
lean_dec_ref(v_toApplicative_4267_);
v___f_4270_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4271_ = ((lean_object*)(l_IO_FS_withTempFile___redArg___closed__0));
lean_inc(v_inst_4265_);
v___x_4272_ = lean_apply_2(v_inst_4265_, lean_box(0), v___x_4271_);
v___f_4273_ = lean_alloc_closure((void*)(l_IO_FS_withTempFile___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4273_, 0, v_toFunctor_4269_);
lean_closure_set(v___f_4273_, 1, v_f_4266_);
lean_closure_set(v___f_4273_, 2, v_inst_4265_);
lean_closure_set(v___f_4273_, 3, v_inst_4264_);
lean_closure_set(v___f_4273_, 4, v___f_4270_);
v___x_4274_ = lean_apply_4(v_toBind_4268_, lean_box(0), lean_box(0), v___x_4272_, v___f_4273_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile(lean_object* v_m_4275_, lean_object* v_00_u03b1_4276_, lean_object* v_inst_4277_, lean_object* v_inst_4278_, lean_object* v_inst_4279_, lean_object* v_f_4280_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l_IO_FS_withTempFile___redArg(v_inst_4277_, v_inst_4278_, v_inst_4279_, v_f_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg___lam__2(lean_object* v_toFunctor_4282_, lean_object* v_f_4283_, lean_object* v_inst_4284_, lean_object* v_inst_4285_, lean_object* v___f_4286_, lean_object* v_path_4287_){
_start:
{
lean_object* v_map_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___f_4292_; lean_object* v_y_4293_; lean_object* v___x_4294_; 
v_map_4288_ = lean_ctor_get(v_toFunctor_4282_, 0);
lean_inc(v_map_4288_);
lean_dec_ref(v_toFunctor_4282_);
lean_inc_ref(v_path_4287_);
v___x_4289_ = lean_apply_1(v_f_4283_, v_path_4287_);
v___x_4290_ = lean_alloc_closure((void*)(l_IO_FS_removeDirAll___boxed), 2, 1);
lean_closure_set(v___x_4290_, 0, v_path_4287_);
v___x_4291_ = lean_apply_2(v_inst_4284_, lean_box(0), v___x_4290_);
v___f_4292_ = lean_alloc_closure((void*)(l_IO_withStdin___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4292_, 0, v___x_4291_);
v_y_4293_ = lean_apply_4(v_inst_4285_, lean_box(0), lean_box(0), v___x_4289_, v___f_4292_);
v___x_4294_ = lean_apply_4(v_map_4288_, lean_box(0), lean_box(0), v___f_4286_, v_y_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___redArg(lean_object* v_inst_4296_, lean_object* v_inst_4297_, lean_object* v_inst_4298_, lean_object* v_f_4299_){
_start:
{
lean_object* v_toApplicative_4300_; lean_object* v_toBind_4301_; lean_object* v_toFunctor_4302_; lean_object* v___f_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___f_4306_; lean_object* v___x_4307_; 
v_toApplicative_4300_ = lean_ctor_get(v_inst_4296_, 0);
lean_inc_ref(v_toApplicative_4300_);
v_toBind_4301_ = lean_ctor_get(v_inst_4296_, 1);
lean_inc(v_toBind_4301_);
lean_dec_ref(v_inst_4296_);
v_toFunctor_4302_ = lean_ctor_get(v_toApplicative_4300_, 0);
lean_inc_ref(v_toFunctor_4302_);
lean_dec_ref(v_toApplicative_4300_);
v___f_4303_ = ((lean_object*)(l_IO_withStdin___redArg___closed__0));
v___x_4304_ = ((lean_object*)(l_IO_FS_withTempDir___redArg___closed__0));
lean_inc(v_inst_4298_);
v___x_4305_ = lean_apply_2(v_inst_4298_, lean_box(0), v___x_4304_);
v___f_4306_ = lean_alloc_closure((void*)(l_IO_FS_withTempDir___redArg___lam__2), 6, 5);
lean_closure_set(v___f_4306_, 0, v_toFunctor_4302_);
lean_closure_set(v___f_4306_, 1, v_f_4299_);
lean_closure_set(v___f_4306_, 2, v_inst_4298_);
lean_closure_set(v___f_4306_, 3, v_inst_4297_);
lean_closure_set(v___f_4306_, 4, v___f_4303_);
v___x_4307_ = lean_apply_4(v_toBind_4301_, lean_box(0), lean_box(0), v___x_4305_, v___f_4306_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir(lean_object* v_m_4308_, lean_object* v_00_u03b1_4309_, lean_object* v_inst_4310_, lean_object* v_inst_4311_, lean_object* v_inst_4312_, lean_object* v_f_4313_){
_start:
{
lean_object* v___x_4314_; 
v___x_4314_ = l_IO_FS_withTempDir___redArg(v_inst_4310_, v_inst_4311_, v_inst_4312_, v_f_4313_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_getCurrentDir___boxed(lean_object* v_a_00___x40___internal___hyg_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = lean_io_process_get_current_dir();
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_setCurrentDir___boxed(lean_object* v_path_4320_, lean_object* v_a_00___x40___internal___hyg_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = lean_io_process_set_current_dir(v_path_4320_);
lean_dec_ref(v_path_4320_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_getPID___boxed(lean_object* v_a_00___x40___internal___hyg_4324_){
_start:
{
uint32_t v_res_4325_; lean_object* v_r_4326_; 
v_res_4325_ = lean_io_process_get_pid();
v_r_4326_ = lean_box_uint32(v_res_4325_);
return v_r_4326_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx(uint8_t v_x_4327_){
_start:
{
switch(v_x_4327_)
{
case 0:
{
lean_object* v___x_4328_; 
v___x_4328_ = lean_unsigned_to_nat(0u);
return v___x_4328_;
}
case 1:
{
lean_object* v___x_4329_; 
v___x_4329_ = lean_unsigned_to_nat(1u);
return v___x_4329_;
}
default: 
{
lean_object* v___x_4330_; 
v___x_4330_ = lean_unsigned_to_nat(2u);
return v___x_4330_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorIdx___boxed(lean_object* v_x_4331_){
_start:
{
uint8_t v_x_boxed_4332_; lean_object* v_res_4333_; 
v_x_boxed_4332_ = lean_unbox(v_x_4331_);
v_res_4333_ = l_IO_Process_Stdio_ctorIdx(v_x_boxed_4332_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx(uint8_t v_x_4334_){
_start:
{
lean_object* v___x_4335_; 
v___x_4335_ = l_IO_Process_Stdio_ctorIdx(v_x_4334_);
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_toCtorIdx___boxed(lean_object* v_x_4336_){
_start:
{
uint8_t v_x_4__boxed_4337_; lean_object* v_res_4338_; 
v_x_4__boxed_4337_ = lean_unbox(v_x_4336_);
v_res_4338_ = l_IO_Process_Stdio_toCtorIdx(v_x_4__boxed_4337_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg(lean_object* v_k_4339_){
_start:
{
lean_inc(v_k_4339_);
return v_k_4339_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___redArg___boxed(lean_object* v_k_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_IO_Process_Stdio_ctorElim___redArg(v_k_4340_);
lean_dec(v_k_4340_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim(lean_object* v_motive_4342_, lean_object* v_ctorIdx_4343_, uint8_t v_t_4344_, lean_object* v_h_4345_, lean_object* v_k_4346_){
_start:
{
lean_inc(v_k_4346_);
return v_k_4346_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_ctorElim___boxed(lean_object* v_motive_4347_, lean_object* v_ctorIdx_4348_, lean_object* v_t_4349_, lean_object* v_h_4350_, lean_object* v_k_4351_){
_start:
{
uint8_t v_t_boxed_4352_; lean_object* v_res_4353_; 
v_t_boxed_4352_ = lean_unbox(v_t_4349_);
v_res_4353_ = l_IO_Process_Stdio_ctorElim(v_motive_4347_, v_ctorIdx_4348_, v_t_boxed_4352_, v_h_4350_, v_k_4351_);
lean_dec(v_k_4351_);
lean_dec(v_ctorIdx_4348_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg(lean_object* v_piped_4354_){
_start:
{
lean_inc(v_piped_4354_);
return v_piped_4354_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___redArg___boxed(lean_object* v_piped_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l_IO_Process_Stdio_piped_elim___redArg(v_piped_4355_);
lean_dec(v_piped_4355_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim(lean_object* v_motive_4357_, uint8_t v_t_4358_, lean_object* v_h_4359_, lean_object* v_piped_4360_){
_start:
{
lean_inc(v_piped_4360_);
return v_piped_4360_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_piped_elim___boxed(lean_object* v_motive_4361_, lean_object* v_t_4362_, lean_object* v_h_4363_, lean_object* v_piped_4364_){
_start:
{
uint8_t v_t_boxed_4365_; lean_object* v_res_4366_; 
v_t_boxed_4365_ = lean_unbox(v_t_4362_);
v_res_4366_ = l_IO_Process_Stdio_piped_elim(v_motive_4361_, v_t_boxed_4365_, v_h_4363_, v_piped_4364_);
lean_dec(v_piped_4364_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg(lean_object* v_inherit_4367_){
_start:
{
lean_inc(v_inherit_4367_);
return v_inherit_4367_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___redArg___boxed(lean_object* v_inherit_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l_IO_Process_Stdio_inherit_elim___redArg(v_inherit_4368_);
lean_dec(v_inherit_4368_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim(lean_object* v_motive_4370_, uint8_t v_t_4371_, lean_object* v_h_4372_, lean_object* v_inherit_4373_){
_start:
{
lean_inc(v_inherit_4373_);
return v_inherit_4373_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_inherit_elim___boxed(lean_object* v_motive_4374_, lean_object* v_t_4375_, lean_object* v_h_4376_, lean_object* v_inherit_4377_){
_start:
{
uint8_t v_t_boxed_4378_; lean_object* v_res_4379_; 
v_t_boxed_4378_ = lean_unbox(v_t_4375_);
v_res_4379_ = l_IO_Process_Stdio_inherit_elim(v_motive_4374_, v_t_boxed_4378_, v_h_4376_, v_inherit_4377_);
lean_dec(v_inherit_4377_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg(lean_object* v_null_4380_){
_start:
{
lean_inc(v_null_4380_);
return v_null_4380_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___redArg___boxed(lean_object* v_null_4381_){
_start:
{
lean_object* v_res_4382_; 
v_res_4382_ = l_IO_Process_Stdio_null_elim___redArg(v_null_4381_);
lean_dec(v_null_4381_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim(lean_object* v_motive_4383_, uint8_t v_t_4384_, lean_object* v_h_4385_, lean_object* v_null_4386_){
_start:
{
lean_inc(v_null_4386_);
return v_null_4386_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Stdio_null_elim___boxed(lean_object* v_motive_4387_, lean_object* v_t_4388_, lean_object* v_h_4389_, lean_object* v_null_4390_){
_start:
{
uint8_t v_t_boxed_4391_; lean_object* v_res_4392_; 
v_t_boxed_4391_ = lean_unbox(v_t_4388_);
v_res_4392_ = l_IO_Process_Stdio_null_elim(v_motive_4387_, v_t_boxed_4391_, v_h_4389_, v_null_4390_);
lean_dec(v_null_4390_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_spawn___boxed(lean_object* v_args_4395_, lean_object* v_a_00___x40___internal___hyg_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = lean_io_process_spawn(v_args_4395_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_wait___boxed(lean_object* v_cfg_4401_, lean_object* v_a_00___x40___internal___hyg_4402_, lean_object* v_a_00___x40___internal___hyg_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = lean_io_process_child_wait(v_cfg_4401_, v_a_00___x40___internal___hyg_4402_);
lean_dec_ref(v_a_00___x40___internal___hyg_4402_);
lean_dec_ref(v_cfg_4401_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_tryWait___boxed(lean_object* v_cfg_4408_, lean_object* v_a_00___x40___internal___hyg_4409_, lean_object* v_a_00___x40___internal___hyg_4410_){
_start:
{
lean_object* v_res_4411_; 
v_res_4411_ = lean_io_process_child_try_wait(v_cfg_4408_, v_a_00___x40___internal___hyg_4409_);
lean_dec_ref(v_a_00___x40___internal___hyg_4409_);
lean_dec_ref(v_cfg_4408_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_kill___boxed(lean_object* v_cfg_4415_, lean_object* v_a_00___x40___internal___hyg_4416_, lean_object* v_a_00___x40___internal___hyg_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = lean_io_process_child_kill(v_cfg_4415_, v_a_00___x40___internal___hyg_4416_);
lean_dec_ref(v_a_00___x40___internal___hyg_4416_);
lean_dec_ref(v_cfg_4415_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_takeStdin___boxed(lean_object* v_cfg_4422_, lean_object* v_a_00___x40___internal___hyg_4423_, lean_object* v_a_00___x40___internal___hyg_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = lean_io_process_child_take_stdin(v_cfg_4422_, v_a_00___x40___internal___hyg_4423_);
lean_dec_ref(v_cfg_4422_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_Child_pid___boxed(lean_object* v_cfg_4428_, lean_object* v_a_00___x40___internal___hyg_4429_){
_start:
{
uint32_t v_res_4430_; lean_object* v_r_4431_; 
v_res_4430_ = lean_io_process_child_pid(v_cfg_4428_, v_a_00___x40___internal___hyg_4429_);
lean_dec_ref(v_cfg_4428_);
v_r_4431_ = lean_box_uint32(v_res_4430_);
return v_r_4431_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(lean_object* v_e_4432_){
_start:
{
if (lean_obj_tag(v_e_4432_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4443_; 
v_a_4434_ = lean_ctor_get(v_e_4432_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v_e_4432_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4436_ = v_e_4432_;
v_isShared_4437_ = v_isSharedCheck_4443_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v_e_4432_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4443_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4441_; 
v___x_4438_ = lean_io_error_to_string(v_a_4434_);
v___x_4439_ = lean_mk_io_user_error(v___x_4438_);
if (v_isShared_4437_ == 0)
{
lean_ctor_set_tag(v___x_4436_, 1);
lean_ctor_set(v___x_4436_, 0, v___x_4439_);
v___x_4441_ = v___x_4436_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4439_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
else
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
v_a_4444_ = lean_ctor_get(v_e_4432_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v_e_4432_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v_e_4432_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v_e_4432_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
lean_ctor_set_tag(v___x_4446_, 0);
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg___boxed(lean_object* v_e_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_4452_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0(lean_object* v_00_u03b1_4455_, lean_object* v_e_4456_){
_start:
{
lean_object* v___x_4458_; 
v___x_4458_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v_e_4456_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00IO_Process_output_spec__0___boxed(lean_object* v_00_u03b1_4459_, lean_object* v_e_4460_, lean_object* v_a_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_IO_ofExcept___at___00IO_Process_output_spec__0(v_00_u03b1_4459_, v_e_4460_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0(lean_object* v_stdout_4463_){
_start:
{
lean_object* v___x_4465_; 
v___x_4465_ = l_IO_FS_Handle_readToEnd(v_stdout_4463_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4473_; 
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4468_ = v___x_4465_;
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4465_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4471_; 
if (v_isShared_4469_ == 0)
{
lean_ctor_set_tag(v___x_4468_, 1);
v___x_4471_ = v___x_4468_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
else
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
v_a_4474_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4465_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4465_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
lean_ctor_set_tag(v___x_4476_, 0);
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_a_4474_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___lam__0___boxed(lean_object* v_stdout_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l_IO_Process_output___lam__0(v_stdout_4482_);
lean_dec(v_stdout_4482_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_output(lean_object* v_args_4490_, lean_object* v_input_x3f_4491_){
_start:
{
lean_object* v_child_4494_; 
if (lean_obj_tag(v_input_x3f_4491_) == 1)
{
lean_object* v_val_4541_; lean_object* v___x_4542_; lean_object* v_cmd_4543_; lean_object* v_args_4544_; lean_object* v_cwd_4545_; lean_object* v_env_4546_; uint8_t v_inheritEnv_4547_; uint8_t v_setsid_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4595_; 
v_val_4541_ = lean_ctor_get(v_input_x3f_4491_, 0);
v___x_4542_ = ((lean_object*)(l_IO_Process_output___closed__1));
v_cmd_4543_ = lean_ctor_get(v_args_4490_, 1);
v_args_4544_ = lean_ctor_get(v_args_4490_, 2);
v_cwd_4545_ = lean_ctor_get(v_args_4490_, 3);
v_env_4546_ = lean_ctor_get(v_args_4490_, 4);
v_inheritEnv_4547_ = lean_ctor_get_uint8(v_args_4490_, sizeof(void*)*5);
v_setsid_4548_ = lean_ctor_get_uint8(v_args_4490_, sizeof(void*)*5 + 1);
v_isSharedCheck_4595_ = !lean_is_exclusive(v_args_4490_);
if (v_isSharedCheck_4595_ == 0)
{
lean_object* v_unused_4596_; 
v_unused_4596_ = lean_ctor_get(v_args_4490_, 0);
lean_dec(v_unused_4596_);
v___x_4550_ = v_args_4490_;
v_isShared_4551_ = v_isSharedCheck_4595_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_env_4546_);
lean_inc(v_cwd_4545_);
lean_inc(v_args_4544_);
lean_inc(v_cmd_4543_);
lean_dec(v_args_4490_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4595_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4553_; 
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4542_);
v___x_4553_ = v___x_4550_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4542_);
lean_ctor_set(v_reuseFailAlloc_4594_, 1, v_cmd_4543_);
lean_ctor_set(v_reuseFailAlloc_4594_, 2, v_args_4544_);
lean_ctor_set(v_reuseFailAlloc_4594_, 3, v_cwd_4545_);
lean_ctor_set(v_reuseFailAlloc_4594_, 4, v_env_4546_);
lean_ctor_set_uint8(v_reuseFailAlloc_4594_, sizeof(void*)*5, v_inheritEnv_4547_);
lean_ctor_set_uint8(v_reuseFailAlloc_4594_, sizeof(void*)*5 + 1, v_setsid_4548_);
v___x_4553_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
lean_object* v___x_4554_; 
v___x_4554_ = lean_io_process_spawn(v___x_4553_);
if (lean_obj_tag(v___x_4554_) == 0)
{
lean_object* v_a_4555_; lean_object* v___x_4556_; 
v_a_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc(v_a_4555_);
lean_dec_ref_known(v___x_4554_, 1);
v___x_4556_ = lean_io_process_child_take_stdin(v___x_4542_, v_a_4555_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v_a_4557_; lean_object* v_fst_4558_; lean_object* v_snd_4559_; lean_object* v___x_4560_; 
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
lean_inc(v_a_4557_);
lean_dec_ref_known(v___x_4556_, 1);
v_fst_4558_ = lean_ctor_get(v_a_4557_, 0);
lean_inc(v_fst_4558_);
v_snd_4559_ = lean_ctor_get(v_a_4557_, 1);
lean_inc(v_snd_4559_);
lean_dec(v_a_4557_);
v___x_4560_ = lean_io_prim_handle_put_str(v_fst_4558_, v_val_4541_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v___x_4561_; 
lean_dec_ref_known(v___x_4560_, 1);
v___x_4561_ = lean_io_prim_handle_flush(v_fst_4558_);
lean_dec(v_fst_4558_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_dec_ref_known(v___x_4561_, 1);
v_child_4494_ = v_snd_4559_;
goto v___jp_4493_;
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_dec(v_snd_4559_);
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4561_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4561_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
lean_dec(v_snd_4559_);
lean_dec(v_fst_4558_);
v_a_4570_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___x_4560_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4560_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
else
{
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4585_; 
v_a_4578_ = lean_ctor_get(v___x_4556_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4580_ = v___x_4556_;
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v___x_4556_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4583_; 
if (v_isShared_4581_ == 0)
{
v___x_4583_ = v___x_4580_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_a_4578_);
v___x_4583_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
return v___x_4583_;
}
}
}
}
else
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
v_a_4586_ = lean_ctor_get(v___x_4554_, 0);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4554_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4588_ = v___x_4554_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v___x_4554_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4586_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
}
}
}
else
{
lean_object* v___x_4597_; lean_object* v_cmd_4598_; lean_object* v_args_4599_; lean_object* v_cwd_4600_; lean_object* v_env_4601_; uint8_t v_inheritEnv_4602_; uint8_t v_setsid_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4620_; 
v___x_4597_ = ((lean_object*)(l_IO_Process_output___closed__0));
v_cmd_4598_ = lean_ctor_get(v_args_4490_, 1);
v_args_4599_ = lean_ctor_get(v_args_4490_, 2);
v_cwd_4600_ = lean_ctor_get(v_args_4490_, 3);
v_env_4601_ = lean_ctor_get(v_args_4490_, 4);
v_inheritEnv_4602_ = lean_ctor_get_uint8(v_args_4490_, sizeof(void*)*5);
v_setsid_4603_ = lean_ctor_get_uint8(v_args_4490_, sizeof(void*)*5 + 1);
v_isSharedCheck_4620_ = !lean_is_exclusive(v_args_4490_);
if (v_isSharedCheck_4620_ == 0)
{
lean_object* v_unused_4621_; 
v_unused_4621_ = lean_ctor_get(v_args_4490_, 0);
lean_dec(v_unused_4621_);
v___x_4605_ = v_args_4490_;
v_isShared_4606_ = v_isSharedCheck_4620_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_env_4601_);
lean_inc(v_cwd_4600_);
lean_inc(v_args_4599_);
lean_inc(v_cmd_4598_);
lean_dec(v_args_4490_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4620_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 0, v___x_4597_);
v___x_4608_ = v___x_4605_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v___x_4597_);
lean_ctor_set(v_reuseFailAlloc_4619_, 1, v_cmd_4598_);
lean_ctor_set(v_reuseFailAlloc_4619_, 2, v_args_4599_);
lean_ctor_set(v_reuseFailAlloc_4619_, 3, v_cwd_4600_);
lean_ctor_set(v_reuseFailAlloc_4619_, 4, v_env_4601_);
lean_ctor_set_uint8(v_reuseFailAlloc_4619_, sizeof(void*)*5, v_inheritEnv_4602_);
lean_ctor_set_uint8(v_reuseFailAlloc_4619_, sizeof(void*)*5 + 1, v_setsid_4603_);
v___x_4608_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
lean_object* v___x_4609_; 
v___x_4609_ = lean_io_process_spawn(v___x_4608_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc(v_a_4610_);
lean_dec_ref_known(v___x_4609_, 1);
v_child_4494_ = v_a_4610_;
goto v___jp_4493_;
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
v_a_4611_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4613_ = v___x_4609_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4609_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
}
}
v___jp_4493_:
{
lean_object* v_stdout_4495_; lean_object* v_stderr_4496_; lean_object* v___f_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
v_stdout_4495_ = lean_ctor_get(v_child_4494_, 1);
v_stderr_4496_ = lean_ctor_get(v_child_4494_, 2);
lean_inc(v_stdout_4495_);
v___f_4497_ = lean_alloc_closure((void*)(l_IO_Process_output___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4497_, 0, v_stdout_4495_);
v___x_4498_ = lean_unsigned_to_nat(9u);
v___x_4499_ = lean_io_as_task(v___f_4497_, v___x_4498_);
v___x_4500_ = l_IO_FS_Handle_readToEnd(v_stderr_4496_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v_a_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
lean_dec_ref_known(v___x_4500_, 1);
v___x_4502_ = ((lean_object*)(l_IO_Process_output___closed__0));
v___x_4503_ = lean_io_process_child_wait(v___x_4502_, v_child_4494_);
lean_dec_ref(v_child_4494_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref_known(v___x_4503_, 1);
v___x_4505_ = lean_task_get_own(v___x_4499_);
v___x_4506_ = l_IO_ofExcept___at___00IO_Process_output_spec__0___redArg(v___x_4505_);
if (lean_obj_tag(v___x_4506_) == 0)
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4516_; 
v_a_4507_ = lean_ctor_get(v___x_4506_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4509_ = v___x_4506_;
v_isShared_4510_ = v_isSharedCheck_4516_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4506_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4516_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4511_; uint32_t v___x_4512_; lean_object* v___x_4514_; 
v___x_4511_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4511_, 0, v_a_4507_);
lean_ctor_set(v___x_4511_, 1, v_a_4501_);
v___x_4512_ = lean_unbox_uint32(v_a_4504_);
lean_dec(v_a_4504_);
lean_ctor_set_uint32(v___x_4511_, sizeof(void*)*2, v___x_4512_);
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 0, v___x_4511_);
v___x_4514_ = v___x_4509_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4511_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
else
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4524_; 
lean_dec(v_a_4504_);
lean_dec(v_a_4501_);
v_a_4517_ = lean_ctor_get(v___x_4506_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4519_ = v___x_4506_;
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v___x_4506_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4522_; 
if (v_isShared_4520_ == 0)
{
v___x_4522_ = v___x_4519_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
else
{
lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4532_; 
lean_dec(v_a_4501_);
lean_dec_ref(v___x_4499_);
v_a_4525_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4527_ = v___x_4503_;
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_dec(v___x_4503_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4530_; 
if (v_isShared_4528_ == 0)
{
v___x_4530_ = v___x_4527_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_a_4525_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
return v___x_4530_;
}
}
}
}
else
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4540_; 
lean_dec_ref(v___x_4499_);
lean_dec_ref(v_child_4494_);
v_a_4533_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4535_ = v___x_4500_;
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4500_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4536_ == 0)
{
v___x_4538_ = v___x_4535_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_a_4533_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_output___boxed(lean_object* v_args_4622_, lean_object* v_input_x3f_4623_, lean_object* v_a_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_IO_Process_output(v_args_4622_, v_input_x3f_4623_);
lean_dec(v_input_x3f_4623_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_run(lean_object* v_args_4629_, lean_object* v_input_x3f_4630_){
_start:
{
lean_object* v___x_4632_; 
lean_inc_ref(v_args_4629_);
v___x_4632_ = l_IO_Process_output(v_args_4629_, v_input_x3f_4630_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_object* v_a_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4660_; 
v_a_4633_ = lean_ctor_get(v___x_4632_, 0);
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4635_ = v___x_4632_;
v_isShared_4636_ = v_isSharedCheck_4660_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_a_4633_);
lean_dec(v___x_4632_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4660_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
uint32_t v_exitCode_4637_; lean_object* v_stdout_4638_; lean_object* v_stderr_4639_; uint32_t v___x_4640_; uint8_t v___x_4641_; 
v_exitCode_4637_ = lean_ctor_get_uint32(v_a_4633_, sizeof(void*)*2);
v_stdout_4638_ = lean_ctor_get(v_a_4633_, 0);
lean_inc_ref(v_stdout_4638_);
v_stderr_4639_ = lean_ctor_get(v_a_4633_, 1);
lean_inc_ref(v_stderr_4639_);
lean_dec(v_a_4633_);
v___x_4640_ = 0;
v___x_4641_ = lean_uint32_dec_eq(v_exitCode_4637_, v___x_4640_);
if (v___x_4641_ == 0)
{
lean_object* v_cmd_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4655_; 
lean_dec_ref(v_stdout_4638_);
v_cmd_4642_ = lean_ctor_get(v_args_4629_, 1);
lean_inc_ref(v_cmd_4642_);
lean_dec_ref(v_args_4629_);
v___x_4643_ = ((lean_object*)(l_IO_Process_run___closed__0));
v___x_4644_ = lean_string_append(v___x_4643_, v_cmd_4642_);
lean_dec_ref(v_cmd_4642_);
v___x_4645_ = ((lean_object*)(l_IO_Process_run___closed__1));
v___x_4646_ = lean_string_append(v___x_4644_, v___x_4645_);
v___x_4647_ = lean_uint32_to_nat(v_exitCode_4637_);
v___x_4648_ = l_Nat_reprFast(v___x_4647_);
v___x_4649_ = lean_string_append(v___x_4646_, v___x_4648_);
lean_dec_ref(v___x_4648_);
v___x_4650_ = ((lean_object*)(l_IO_Process_run___closed__2));
v___x_4651_ = lean_string_append(v___x_4649_, v___x_4650_);
v___x_4652_ = lean_string_append(v___x_4651_, v_stderr_4639_);
lean_dec_ref(v_stderr_4639_);
v___x_4653_ = lean_mk_io_user_error(v___x_4652_);
if (v_isShared_4636_ == 0)
{
lean_ctor_set_tag(v___x_4635_, 1);
lean_ctor_set(v___x_4635_, 0, v___x_4653_);
v___x_4655_ = v___x_4635_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v___x_4653_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
else
{
lean_object* v___x_4658_; 
lean_dec_ref(v_stderr_4639_);
lean_dec_ref(v_args_4629_);
if (v_isShared_4636_ == 0)
{
lean_ctor_set(v___x_4635_, 0, v_stdout_4638_);
v___x_4658_ = v___x_4635_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_stdout_4638_);
v___x_4658_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
return v___x_4658_;
}
}
}
}
else
{
lean_object* v_a_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4668_; 
lean_dec_ref(v_args_4629_);
v_a_4661_ = lean_ctor_get(v___x_4632_, 0);
v_isSharedCheck_4668_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4668_ == 0)
{
v___x_4663_ = v___x_4632_;
v_isShared_4664_ = v_isSharedCheck_4668_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_a_4661_);
lean_dec(v___x_4632_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4668_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v___x_4666_; 
if (v_isShared_4664_ == 0)
{
v___x_4666_ = v___x_4663_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v_a_4661_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
return v___x_4666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_Process_run___boxed(lean_object* v_args_4669_, lean_object* v_input_x3f_4670_, lean_object* v_a_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l_IO_Process_run(v_args_4669_, v_input_x3f_4670_);
lean_dec(v_input_x3f_4670_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_exit___boxed(lean_object* v_00_u03b1_4676_, lean_object* v_a_00___x40___internal___hyg_4677_, lean_object* v_a_00___x40___internal___hyg_4678_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_4679_; lean_object* v_res_4680_; 
v_a_00___x40___internal___hyg_1__boxed_4679_ = lean_unbox(v_a_00___x40___internal___hyg_4677_);
v_res_4680_ = lean_io_exit(v_a_00___x40___internal___hyg_1__boxed_4679_);
return v_res_4680_;
}
}
LEAN_EXPORT lean_object* l_IO_Process_forceExit___boxed(lean_object* v_00_u03b1_4684_, lean_object* v_a_00___x40___internal___hyg_4685_, lean_object* v_a_00___x40___internal___hyg_4686_){
_start:
{
uint8_t v_a_00___x40___internal___hyg_1__boxed_4687_; lean_object* v_res_4688_; 
v_a_00___x40___internal___hyg_1__boxed_4687_ = lean_unbox(v_a_00___x40___internal___hyg_4685_);
v_res_4688_ = lean_io_force_exit(v_a_00___x40___internal___hyg_1__boxed_4687_);
return v_res_4688_;
}
}
LEAN_EXPORT lean_object* l_IO_getTID___boxed(lean_object* v_a_00___x40___internal___hyg_4690_){
_start:
{
uint64_t v_res_4691_; lean_object* v_r_4692_; 
v_res_4691_ = lean_io_get_tid();
v_r_4692_ = lean_box_uint64(v_res_4691_);
return v_r_4692_;
}
}
LEAN_EXPORT uint32_t l_IO_AccessRight_flags(lean_object* v_acc_4693_){
_start:
{
uint32_t v___y_4695_; uint32_t v___y_4696_; uint32_t v___y_4697_; uint8_t v_read_4700_; uint8_t v_write_4701_; uint8_t v_execution_4702_; uint32_t v___y_4704_; uint32_t v___y_4705_; uint32_t v___y_4709_; 
v_read_4700_ = lean_ctor_get_uint8(v_acc_4693_, 0);
v_write_4701_ = lean_ctor_get_uint8(v_acc_4693_, 1);
v_execution_4702_ = lean_ctor_get_uint8(v_acc_4693_, 2);
if (v_read_4700_ == 0)
{
uint32_t v___x_4712_; 
v___x_4712_ = 0;
v___y_4709_ = v___x_4712_;
goto v___jp_4708_;
}
else
{
uint32_t v___x_4713_; 
v___x_4713_ = 4;
v___y_4709_ = v___x_4713_;
goto v___jp_4708_;
}
v___jp_4694_:
{
uint32_t v___x_4698_; uint32_t v___x_4699_; 
v___x_4698_ = lean_uint32_lor(v___y_4695_, v___y_4697_);
v___x_4699_ = lean_uint32_lor(v___y_4696_, v___x_4698_);
return v___x_4699_;
}
v___jp_4703_:
{
if (v_execution_4702_ == 0)
{
uint32_t v___x_4706_; 
v___x_4706_ = 0;
v___y_4695_ = v___y_4705_;
v___y_4696_ = v___y_4704_;
v___y_4697_ = v___x_4706_;
goto v___jp_4694_;
}
else
{
uint32_t v___x_4707_; 
v___x_4707_ = 1;
v___y_4695_ = v___y_4705_;
v___y_4696_ = v___y_4704_;
v___y_4697_ = v___x_4707_;
goto v___jp_4694_;
}
}
v___jp_4708_:
{
if (v_write_4701_ == 0)
{
uint32_t v___x_4710_; 
v___x_4710_ = 0;
v___y_4704_ = v___y_4709_;
v___y_4705_ = v___x_4710_;
goto v___jp_4703_;
}
else
{
uint32_t v___x_4711_; 
v___x_4711_ = 2;
v___y_4704_ = v___y_4709_;
v___y_4705_ = v___x_4711_;
goto v___jp_4703_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AccessRight_flags___boxed(lean_object* v_acc_4714_){
_start:
{
uint32_t v_res_4715_; lean_object* v_r_4716_; 
v_res_4715_ = l_IO_AccessRight_flags(v_acc_4714_);
lean_dec_ref(v_acc_4714_);
v_r_4716_ = lean_box_uint32(v_res_4715_);
return v_r_4716_;
}
}
LEAN_EXPORT uint32_t l_IO_FileRight_flags(lean_object* v_acc_4717_){
_start:
{
lean_object* v_user_4718_; lean_object* v_group_4719_; lean_object* v_other_4720_; uint32_t v___x_4721_; uint32_t v___x_4722_; uint32_t v_u_4723_; uint32_t v___x_4724_; uint32_t v___x_4725_; uint32_t v_g_4726_; uint32_t v_o_4727_; uint32_t v___x_4728_; uint32_t v___x_4729_; 
v_user_4718_ = lean_ctor_get(v_acc_4717_, 0);
v_group_4719_ = lean_ctor_get(v_acc_4717_, 1);
v_other_4720_ = lean_ctor_get(v_acc_4717_, 2);
v___x_4721_ = l_IO_AccessRight_flags(v_user_4718_);
v___x_4722_ = 6;
v_u_4723_ = lean_uint32_shift_left(v___x_4721_, v___x_4722_);
v___x_4724_ = l_IO_AccessRight_flags(v_group_4719_);
v___x_4725_ = 3;
v_g_4726_ = lean_uint32_shift_left(v___x_4724_, v___x_4725_);
v_o_4727_ = l_IO_AccessRight_flags(v_other_4720_);
v___x_4728_ = lean_uint32_lor(v_g_4726_, v_o_4727_);
v___x_4729_ = lean_uint32_lor(v_u_4723_, v___x_4728_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l_IO_FileRight_flags___boxed(lean_object* v_acc_4730_){
_start:
{
uint32_t v_res_4731_; lean_object* v_r_4732_; 
v_res_4731_ = l_IO_FileRight_flags(v_acc_4730_);
lean_dec_ref(v_acc_4730_);
v_r_4732_ = lean_box_uint32(v_res_4731_);
return v_r_4732_;
}
}
LEAN_EXPORT lean_object* l_IO_Prim_setAccessRights___boxed(lean_object* v_filename_4736_, lean_object* v_mode_4737_, lean_object* v_a_00___x40___internal___hyg_4738_){
_start:
{
uint32_t v_mode_boxed_4739_; lean_object* v_res_4740_; 
v_mode_boxed_4739_ = lean_unbox_uint32(v_mode_4737_);
lean_dec(v_mode_4737_);
v_res_4740_ = lean_chmod(v_filename_4736_, v_mode_boxed_4739_);
lean_dec_ref(v_filename_4736_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights(lean_object* v_filename_4741_, lean_object* v_mode_4742_){
_start:
{
uint32_t v___x_4744_; lean_object* v___x_4745_; 
v___x_4744_ = l_IO_FileRight_flags(v_mode_4742_);
v___x_4745_ = lean_chmod(v_filename_4741_, v___x_4744_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l_IO_setAccessRights___boxed(lean_object* v_filename_4746_, lean_object* v_mode_4747_, lean_object* v_a_4748_){
_start:
{
lean_object* v_res_4749_; 
v_res_4749_ = l_IO_setAccessRights(v_filename_4746_, v_mode_4747_);
lean_dec_ref(v_mode_4747_);
lean_dec_ref(v_filename_4746_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(lean_object* v_00_u03b1_4750_, lean_object* v_mx_4751_){
_start:
{
lean_object* v___x_4753_; 
v___x_4753_ = lean_apply_1(v_mx_4751_, lean_box(0));
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object* v_00_u03b1_4754_, lean_object* v_mx_4755_, lean_object* v_s_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_IO_instMonadLiftSTRealWorldBaseIO___lam__0(v_00_u03b1_4754_, v_mx_4755_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg(lean_object* v_a_4760_){
_start:
{
lean_object* v___x_4762_; 
v___x_4762_ = lean_st_mk_ref(v_a_4760_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___redArg___boxed(lean_object* v_a_4763_, lean_object* v_a_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l_IO_mkRef___redArg(v_a_4763_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef(lean_object* v_00_u03b1_4766_, lean_object* v_a_4767_){
_start:
{
lean_object* v___x_4769_; 
v___x_4769_ = lean_st_mk_ref(v_a_4767_);
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l_IO_mkRef___boxed(lean_object* v_00_u03b1_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l_IO_mkRef(v_00_u03b1_4770_, v_a_4771_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* lean_stream_of_handle(lean_object* v_h_4774_){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
lean_inc_n(v_h_4774_, 5);
v___x_4775_ = lean_alloc_closure((void*)(l_IO_FS_Handle_flush___boxed), 2, 1);
lean_closure_set(v___x_4775_, 0, v_h_4774_);
v___x_4776_ = lean_alloc_closure((void*)(l_IO_FS_Handle_read___boxed), 3, 1);
lean_closure_set(v___x_4776_, 0, v_h_4774_);
v___x_4777_ = lean_alloc_closure((void*)(l_IO_FS_Handle_write___boxed), 3, 1);
lean_closure_set(v___x_4777_, 0, v_h_4774_);
v___x_4778_ = lean_alloc_closure((void*)(l_IO_FS_Handle_getLine___boxed), 2, 1);
lean_closure_set(v___x_4778_, 0, v_h_4774_);
v___x_4779_ = lean_alloc_closure((void*)(l_IO_FS_Handle_putStr___boxed), 3, 1);
lean_closure_set(v___x_4779_, 0, v_h_4774_);
v___x_4780_ = lean_alloc_closure((void*)(l_IO_FS_Handle_isTty___boxed), 2, 1);
lean_closure_set(v___x_4780_, 0, v_h_4774_);
v___x_4781_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4781_, 0, v___x_4775_);
lean_ctor_set(v___x_4781_, 1, v___x_4776_);
lean_ctor_set(v___x_4781_, 2, v___x_4777_);
lean_ctor_set(v___x_4781_, 3, v___x_4778_);
lean_ctor_set(v___x_4781_, 4, v___x_4779_);
lean_ctor_set(v___x_4781_, 5, v___x_4780_);
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0(lean_object* v_r_4782_, size_t v_n_4783_){
_start:
{
lean_object* v___x_4785_; lean_object* v_data_4786_; lean_object* v_pos_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4801_; 
v___x_4785_ = lean_st_ref_take(v_r_4782_);
v_data_4786_ = lean_ctor_get(v___x_4785_, 0);
v_pos_4787_ = lean_ctor_get(v___x_4785_, 1);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4789_ = v___x_4785_;
v_isShared_4790_ = v_isSharedCheck_4801_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_pos_4787_);
lean_inc(v_data_4786_);
lean_dec(v___x_4785_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4801_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v_data_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4797_; 
v___x_4791_ = lean_usize_to_nat(v_n_4783_);
v___x_4792_ = lean_nat_add(v_pos_4787_, v___x_4791_);
lean_dec(v___x_4791_);
lean_inc(v_pos_4787_);
v_data_4793_ = l_ByteArray_extract(v_data_4786_, v_pos_4787_, v___x_4792_);
lean_dec(v___x_4792_);
v___x_4794_ = lean_byte_array_size(v_data_4793_);
v___x_4795_ = lean_nat_add(v_pos_4787_, v___x_4794_);
lean_dec(v_pos_4787_);
if (v_isShared_4790_ == 0)
{
lean_ctor_set(v___x_4789_, 1, v___x_4795_);
v___x_4797_ = v___x_4789_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v_data_4786_);
lean_ctor_set(v_reuseFailAlloc_4800_, 1, v___x_4795_);
v___x_4797_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
lean_object* v___x_4798_; lean_object* v___x_4799_; 
v___x_4798_ = lean_st_ref_set(v_r_4782_, v___x_4797_);
v___x_4799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4799_, 0, v_data_4793_);
return v___x_4799_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__0___boxed(lean_object* v_r_4802_, lean_object* v_n_4803_, lean_object* v___y_4804_){
_start:
{
size_t v_n_boxed_4805_; lean_object* v_res_4806_; 
v_n_boxed_4805_ = lean_unbox_usize(v_n_4803_);
lean_dec(v_n_4803_);
v_res_4806_ = l_IO_FS_Stream_ofBuffer___lam__0(v_r_4802_, v_n_boxed_4805_);
lean_dec(v_r_4802_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1(lean_object* v_r_4807_, lean_object* v_data_4808_){
_start:
{
lean_object* v___x_4810_; lean_object* v_data_4811_; lean_object* v_pos_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4826_; 
v___x_4810_ = lean_st_ref_take(v_r_4807_);
v_data_4811_ = lean_ctor_get(v___x_4810_, 0);
v_pos_4812_ = lean_ctor_get(v___x_4810_, 1);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4814_ = v___x_4810_;
v_isShared_4815_ = v_isSharedCheck_4826_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_pos_4812_);
lean_inc(v_data_4811_);
lean_dec(v___x_4810_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4826_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4822_; 
v___x_4816_ = lean_unsigned_to_nat(0u);
v___x_4817_ = lean_byte_array_size(v_data_4808_);
v___x_4818_ = 0;
lean_inc(v_pos_4812_);
v___x_4819_ = lean_byte_array_copy_slice(v_data_4808_, v___x_4816_, v_data_4811_, v_pos_4812_, v___x_4817_, v___x_4818_);
v___x_4820_ = lean_nat_add(v_pos_4812_, v___x_4817_);
lean_dec(v_pos_4812_);
if (v_isShared_4815_ == 0)
{
lean_ctor_set(v___x_4814_, 1, v___x_4820_);
lean_ctor_set(v___x_4814_, 0, v___x_4819_);
v___x_4822_ = v___x_4814_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v___x_4819_);
lean_ctor_set(v_reuseFailAlloc_4825_, 1, v___x_4820_);
v___x_4822_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4823_ = lean_st_ref_set(v_r_4807_, v___x_4822_);
v___x_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4823_);
return v___x_4824_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__1___boxed(lean_object* v_r_4827_, lean_object* v_data_4828_, lean_object* v___y_4829_){
_start:
{
lean_object* v_res_4830_; 
v_res_4830_ = l_IO_FS_Stream_ofBuffer___lam__1(v_r_4827_, v_data_4828_);
lean_dec_ref(v_data_4828_);
lean_dec(v_r_4827_);
return v_res_4830_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2(lean_object* v_r_4831_, lean_object* v_s_4832_){
_start:
{
lean_object* v___x_4834_; lean_object* v_data_4835_; lean_object* v_pos_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4851_; 
v___x_4834_ = lean_st_ref_take(v_r_4831_);
v_data_4835_ = lean_ctor_get(v___x_4834_, 0);
v_pos_4836_ = lean_ctor_get(v___x_4834_, 1);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4834_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4838_ = v___x_4834_;
v_isShared_4839_ = v_isSharedCheck_4851_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_pos_4836_);
lean_inc(v_data_4835_);
lean_dec(v___x_4834_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4851_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v_data_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; uint8_t v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4847_; 
v_data_4840_ = lean_string_to_utf8(v_s_4832_);
v___x_4841_ = lean_unsigned_to_nat(0u);
v___x_4842_ = lean_byte_array_size(v_data_4840_);
v___x_4843_ = 0;
lean_inc(v_pos_4836_);
v___x_4844_ = lean_byte_array_copy_slice(v_data_4840_, v___x_4841_, v_data_4835_, v_pos_4836_, v___x_4842_, v___x_4843_);
lean_dec_ref(v_data_4840_);
v___x_4845_ = lean_nat_add(v_pos_4836_, v___x_4842_);
lean_dec(v_pos_4836_);
if (v_isShared_4839_ == 0)
{
lean_ctor_set(v___x_4838_, 1, v___x_4845_);
lean_ctor_set(v___x_4838_, 0, v___x_4844_);
v___x_4847_ = v___x_4838_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4844_);
lean_ctor_set(v_reuseFailAlloc_4850_, 1, v___x_4845_);
v___x_4847_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4848_ = lean_st_ref_set(v_r_4831_, v___x_4847_);
v___x_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4848_);
return v___x_4849_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__2___boxed(lean_object* v_r_4852_, lean_object* v_s_4853_, lean_object* v___y_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l_IO_FS_Stream_ofBuffer___lam__2(v_r_4852_, v_s_4853_);
lean_dec_ref(v_s_4853_);
lean_dec(v_r_4852_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(lean_object* v_a_4856_, lean_object* v_i_4857_){
_start:
{
uint8_t v___y_4859_; lean_object* v___x_4864_; uint8_t v___x_4865_; 
v___x_4864_ = lean_byte_array_size(v_a_4856_);
v___x_4865_ = lean_nat_dec_lt(v_i_4857_, v___x_4864_);
if (v___x_4865_ == 0)
{
lean_object* v___x_4866_; 
lean_dec(v_i_4857_);
v___x_4866_ = lean_box(0);
return v___x_4866_;
}
else
{
uint8_t v___x_4867_; uint8_t v___x_4868_; uint8_t v___x_4869_; 
v___x_4867_ = lean_byte_array_fget(v_a_4856_, v_i_4857_);
v___x_4868_ = 0;
v___x_4869_ = lean_uint8_dec_eq(v___x_4867_, v___x_4868_);
if (v___x_4869_ == 0)
{
uint8_t v___x_4870_; uint8_t v___x_4871_; 
v___x_4870_ = 10;
v___x_4871_ = lean_uint8_dec_eq(v___x_4867_, v___x_4870_);
v___y_4859_ = v___x_4871_;
goto v___jp_4858_;
}
else
{
v___y_4859_ = v___x_4869_;
goto v___jp_4858_;
}
}
v___jp_4858_:
{
if (v___y_4859_ == 0)
{
lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4860_ = lean_unsigned_to_nat(1u);
v___x_4861_ = lean_nat_add(v_i_4857_, v___x_4860_);
lean_dec(v_i_4857_);
v_i_4857_ = v___x_4861_;
goto _start;
}
else
{
lean_object* v___x_4863_; 
v___x_4863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4863_, 0, v_i_4857_);
return v___x_4863_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0___boxed(lean_object* v_a_4872_, lean_object* v_i_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(v_a_4872_, v_i_4873_);
lean_dec_ref(v_a_4872_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3(lean_object* v_r_4878_){
_start:
{
lean_object* v___x_4880_; lean_object* v_data_4881_; lean_object* v_pos_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4906_; 
v___x_4880_ = lean_st_ref_take(v_r_4878_);
v_data_4881_ = lean_ctor_get(v___x_4880_, 0);
v_pos_4882_ = lean_ctor_get(v___x_4880_, 1);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4884_ = v___x_4880_;
v_isShared_4885_ = v_isSharedCheck_4906_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_pos_4882_);
lean_inc(v_data_4881_);
lean_dec(v___x_4880_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4906_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___y_4887_; lean_object* v___x_4898_; 
lean_inc(v_pos_4882_);
v___x_4898_ = l_ByteArray_findIdx_x3f_loop___at___00IO_FS_Stream_ofBuffer_spec__0(v_data_4881_, v_pos_4882_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v___x_4899_; 
v___x_4899_ = lean_byte_array_size(v_data_4881_);
v___y_4887_ = v___x_4899_;
goto v___jp_4886_;
}
else
{
lean_object* v_val_4900_; uint8_t v___x_4901_; uint8_t v___x_4902_; uint8_t v___x_4903_; 
v_val_4900_ = lean_ctor_get(v___x_4898_, 0);
lean_inc(v_val_4900_);
lean_dec_ref_known(v___x_4898_, 1);
v___x_4901_ = lean_byte_array_get(v_data_4881_, v_val_4900_);
v___x_4902_ = 0;
v___x_4903_ = lean_uint8_dec_eq(v___x_4901_, v___x_4902_);
if (v___x_4903_ == 0)
{
lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4904_ = lean_unsigned_to_nat(1u);
v___x_4905_ = lean_nat_add(v_val_4900_, v___x_4904_);
lean_dec(v_val_4900_);
v___y_4887_ = v___x_4905_;
goto v___jp_4886_;
}
else
{
v___y_4887_ = v_val_4900_;
goto v___jp_4886_;
}
}
v___jp_4886_:
{
lean_object* v___x_4888_; lean_object* v___x_4890_; 
v___x_4888_ = l_ByteArray_extract(v_data_4881_, v_pos_4882_, v___y_4887_);
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 1, v___y_4887_);
v___x_4890_ = v___x_4884_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_data_4881_);
lean_ctor_set(v_reuseFailAlloc_4897_, 1, v___y_4887_);
v___x_4890_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
lean_object* v___x_4891_; uint8_t v___x_4892_; 
v___x_4891_ = lean_st_ref_set(v_r_4878_, v___x_4890_);
v___x_4892_ = lean_string_validate_utf8(v___x_4888_);
if (v___x_4892_ == 0)
{
lean_object* v___x_4893_; lean_object* v___x_4894_; 
lean_dec_ref(v___x_4888_);
v___x_4893_ = ((lean_object*)(l_IO_FS_Stream_ofBuffer___lam__3___closed__1));
v___x_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4893_);
return v___x_4894_;
}
else
{
lean_object* v___x_4895_; lean_object* v___x_4896_; 
v___x_4895_ = lean_string_from_utf8_unchecked(v___x_4888_);
v___x_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4895_);
return v___x_4896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__3___boxed(lean_object* v_r_4907_, lean_object* v___y_4908_){
_start:
{
lean_object* v_res_4909_; 
v_res_4909_ = l_IO_FS_Stream_ofBuffer___lam__3(v_r_4907_);
lean_dec(v_r_4907_);
return v_res_4909_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4(lean_object* v___x_4910_){
_start:
{
lean_object* v___x_4912_; 
v___x_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4910_);
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer___lam__4___boxed(lean_object* v___x_4913_, lean_object* v___y_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_IO_FS_Stream_ofBuffer___lam__4(v___x_4913_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_ofBuffer(lean_object* v_r_4918_){
_start:
{
lean_object* v___f_4919_; lean_object* v___f_4920_; lean_object* v___f_4921_; lean_object* v___f_4922_; lean_object* v___f_4923_; lean_object* v___f_4924_; lean_object* v___x_4925_; 
lean_inc_n(v_r_4918_, 3);
v___f_4919_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4919_, 0, v_r_4918_);
v___f_4920_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4920_, 0, v_r_4918_);
v___f_4921_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4921_, 0, v_r_4918_);
v___f_4922_ = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lam__3___boxed), 2, 1);
lean_closure_set(v___f_4922_, 0, v_r_4918_);
v___f_4923_ = ((lean_object*)(l_IO_FS_Stream_ofBuffer___closed__0));
v___f_4924_ = ((lean_object*)(l_IO_FS_instInhabitedStream_default___closed__5));
v___x_4925_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4925_, 0, v___f_4923_);
lean_ctor_set(v___x_4925_, 1, v___f_4919_);
lean_ctor_set(v___x_4925_, 2, v___f_4920_);
lean_ctor_set(v___x_4925_, 3, v___f_4922_);
lean_ctor_set(v___x_4925_, 4, v___f_4921_);
lean_ctor_set(v___x_4925_, 5, v___f_4924_);
return v___x_4925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(lean_object* v_s_4928_, lean_object* v_acc_4929_){
_start:
{
lean_object* v_read_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v_read_4931_ = lean_ctor_get(v_s_4928_, 1);
v___x_4932_ = ((lean_object*)(l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed__const__1));
lean_inc_ref(v_read_4931_);
v___x_4933_ = lean_apply_2(v_read_4931_, v___x_4932_, lean_box(0));
if (lean_obj_tag(v___x_4933_) == 0)
{
lean_object* v_a_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4947_; 
v_a_4934_ = lean_ctor_get(v___x_4933_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4933_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4936_ = v___x_4933_;
v_isShared_4937_ = v_isSharedCheck_4947_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_a_4934_);
lean_dec(v___x_4933_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4947_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
uint8_t v___x_4938_; 
v___x_4938_ = l_ByteArray_isEmpty(v_a_4934_);
if (v___x_4938_ == 0)
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; 
lean_del_object(v___x_4936_);
v___x_4939_ = lean_unsigned_to_nat(0u);
v___x_4940_ = lean_byte_array_size(v_acc_4929_);
v___x_4941_ = lean_byte_array_size(v_a_4934_);
v___x_4942_ = lean_byte_array_copy_slice(v_a_4934_, v___x_4939_, v_acc_4929_, v___x_4940_, v___x_4941_, v___x_4938_);
lean_dec(v_a_4934_);
v_acc_4929_ = v___x_4942_;
goto _start;
}
else
{
lean_object* v___x_4945_; 
lean_dec(v_a_4934_);
lean_dec_ref(v_s_4928_);
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 0, v_acc_4929_);
v___x_4945_ = v___x_4936_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_acc_4929_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
}
}
else
{
lean_dec_ref(v_acc_4929_);
lean_dec_ref(v_s_4928_);
return v___x_4933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop___boxed(lean_object* v_s_4948_, lean_object* v_acc_4949_, lean_object* v_a_4950_){
_start:
{
lean_object* v_res_4951_; 
v_res_4951_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4948_, v_acc_4949_);
return v_res_4951_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto(lean_object* v_s_4952_, lean_object* v_buf_4953_){
_start:
{
lean_object* v___x_4955_; 
v___x_4955_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4952_, v_buf_4953_);
return v___x_4955_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEndInto___boxed(lean_object* v_s_4956_, lean_object* v_buf_4957_, lean_object* v_a_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l_IO_FS_Stream_readBinToEndInto(v_s_4956_, v_buf_4957_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd(lean_object* v_s_4960_){
_start:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4962_ = l_ByteArray_empty;
v___x_4963_ = l___private_Init_System_IO_0__IO_FS_Stream_readBinToEndInto_loop(v_s_4960_, v___x_4962_);
return v___x_4963_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readBinToEnd___boxed(lean_object* v_s_4964_, lean_object* v_a_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l_IO_FS_Stream_readBinToEnd(v_s_4964_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd(lean_object* v_s_4970_){
_start:
{
lean_object* v___x_4972_; 
v___x_4972_ = l_IO_FS_Stream_readBinToEnd(v_s_4970_);
if (lean_obj_tag(v___x_4972_) == 0)
{
lean_object* v_a_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4986_; 
v_a_4973_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_4986_ == 0)
{
v___x_4975_ = v___x_4972_;
v_isShared_4976_ = v_isSharedCheck_4986_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_a_4973_);
lean_dec(v___x_4972_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4986_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
uint8_t v___x_4977_; 
v___x_4977_ = lean_string_validate_utf8(v_a_4973_);
if (v___x_4977_ == 0)
{
lean_object* v___x_4978_; lean_object* v___x_4980_; 
lean_dec(v_a_4973_);
v___x_4978_ = ((lean_object*)(l_IO_FS_Stream_readToEnd___closed__1));
if (v_isShared_4976_ == 0)
{
lean_ctor_set_tag(v___x_4975_, 1);
lean_ctor_set(v___x_4975_, 0, v___x_4978_);
v___x_4980_ = v___x_4975_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v___x_4978_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
else
{
lean_object* v___x_4982_; lean_object* v___x_4984_; 
v___x_4982_ = lean_string_from_utf8_unchecked(v_a_4973_);
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 0, v___x_4982_);
v___x_4984_ = v___x_4975_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v___x_4982_);
v___x_4984_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
return v___x_4984_;
}
}
}
}
else
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4994_; 
v_a_4987_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4989_ = v___x_4972_;
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v___x_4972_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4992_; 
if (v_isShared_4990_ == 0)
{
v___x_4992_ = v___x_4989_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4987_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readToEnd___boxed(lean_object* v_s_4995_, lean_object* v_a_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l_IO_FS_Stream_readToEnd(v_s_4995_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read(lean_object* v_s_4998_, lean_object* v_lines_4999_){
_start:
{
lean_object* v_getLine_5001_; lean_object* v___x_5002_; 
v_getLine_5001_ = lean_ctor_get(v_s_4998_, 3);
lean_inc_ref(v_getLine_5001_);
v___x_5002_ = lean_apply_1(v_getLine_5001_, lean_box(0));
if (lean_obj_tag(v___x_5002_) == 0)
{
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5057_; 
v_a_5003_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5005_ = v___x_5002_;
v_isShared_5006_ = v_isSharedCheck_5057_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_5002_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5057_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___y_5008_; lean_object* v___y_5012_; lean_object* v___y_5013_; lean_object* v___y_5014_; uint32_t v___y_5015_; uint32_t v___y_5023_; lean_object* v___x_5045_; lean_object* v___x_5046_; uint8_t v___x_5047_; 
v___x_5045_ = lean_string_utf8_byte_size(v_a_5003_);
v___x_5046_ = lean_unsigned_to_nat(0u);
v___x_5047_ = lean_nat_dec_eq(v___x_5045_, v___x_5046_);
if (v___x_5047_ == 0)
{
lean_object* v___x_5048_; lean_object* v___x_5049_; 
lean_inc(v_a_5003_);
v___x_5048_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5048_, 0, v_a_5003_);
lean_ctor_set(v___x_5048_, 1, v___x_5046_);
lean_ctor_set(v___x_5048_, 2, v___x_5045_);
v___x_5049_ = l_String_Slice_Pos_prev_x3f(v___x_5048_, v___x_5045_);
if (lean_obj_tag(v___x_5049_) == 0)
{
uint32_t v___x_5050_; 
lean_dec_ref_known(v___x_5048_, 3);
v___x_5050_ = 65;
v___y_5023_ = v___x_5050_;
goto v___jp_5022_;
}
else
{
lean_object* v_val_5051_; lean_object* v___x_5052_; 
v_val_5051_ = lean_ctor_get(v___x_5049_, 0);
lean_inc(v_val_5051_);
lean_dec_ref_known(v___x_5049_, 1);
v___x_5052_ = l_String_Slice_Pos_get_x3f(v___x_5048_, v_val_5051_);
lean_dec(v_val_5051_);
lean_dec_ref_known(v___x_5048_, 3);
if (lean_obj_tag(v___x_5052_) == 0)
{
uint32_t v___x_5053_; 
v___x_5053_ = 65;
v___y_5023_ = v___x_5053_;
goto v___jp_5022_;
}
else
{
lean_object* v_val_5054_; uint32_t v___x_5055_; 
v_val_5054_ = lean_ctor_get(v___x_5052_, 0);
lean_inc(v_val_5054_);
lean_dec_ref_known(v___x_5052_, 1);
v___x_5055_ = lean_unbox_uint32(v_val_5054_);
lean_dec(v_val_5054_);
v___y_5023_ = v___x_5055_;
goto v___jp_5022_;
}
}
}
else
{
lean_object* v___x_5056_; 
lean_del_object(v___x_5005_);
lean_dec(v_a_5003_);
lean_dec_ref(v_s_4998_);
v___x_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5056_, 0, v_lines_4999_);
return v___x_5056_;
}
v___jp_5007_:
{
lean_object* v___x_5009_; 
v___x_5009_ = lean_array_push(v_lines_4999_, v___y_5008_);
v_lines_4999_ = v___x_5009_;
goto _start;
}
v___jp_5011_:
{
uint32_t v___x_5016_; uint8_t v___x_5017_; 
v___x_5016_ = 13;
v___x_5017_ = lean_uint32_dec_eq(v___y_5015_, v___x_5016_);
if (v___x_5017_ == 0)
{
lean_dec(v___y_5014_);
lean_dec(v___y_5012_);
v___y_5008_ = v___y_5013_;
goto v___jp_5007_;
}
else
{
lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5018_ = lean_string_utf8_byte_size(v___y_5013_);
lean_inc(v___y_5014_);
lean_inc_ref(v___y_5013_);
v___x_5019_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5019_, 0, v___y_5013_);
lean_ctor_set(v___x_5019_, 1, v___y_5014_);
lean_ctor_set(v___x_5019_, 2, v___x_5018_);
v___x_5020_ = l_String_Slice_Pos_prevn(v___x_5019_, v___x_5018_, v___y_5012_);
lean_dec_ref_known(v___x_5019_, 3);
v___x_5021_ = lean_string_utf8_extract(v___y_5013_, v___y_5014_, v___x_5020_);
lean_dec(v___x_5020_);
lean_dec(v___y_5014_);
lean_dec_ref(v___y_5013_);
v___y_5008_ = v___x_5021_;
goto v___jp_5007_;
}
}
v___jp_5022_:
{
uint32_t v___x_5024_; uint8_t v___x_5025_; 
v___x_5024_ = 10;
v___x_5025_ = lean_uint32_dec_eq(v___y_5023_, v___x_5024_);
if (v___x_5025_ == 0)
{
lean_object* v___x_5026_; lean_object* v___x_5028_; 
lean_dec_ref(v_s_4998_);
v___x_5026_ = lean_array_push(v_lines_4999_, v_a_5003_);
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 0, v___x_5026_);
v___x_5028_ = v___x_5005_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v___x_5026_);
v___x_5028_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
return v___x_5028_;
}
}
else
{
lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
lean_del_object(v___x_5005_);
v___x_5030_ = lean_unsigned_to_nat(1u);
v___x_5031_ = lean_unsigned_to_nat(0u);
v___x_5032_ = lean_string_utf8_byte_size(v_a_5003_);
lean_inc(v_a_5003_);
v___x_5033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5033_, 0, v_a_5003_);
lean_ctor_set(v___x_5033_, 1, v___x_5031_);
lean_ctor_set(v___x_5033_, 2, v___x_5032_);
v___x_5034_ = l_String_Slice_Pos_prevn(v___x_5033_, v___x_5032_, v___x_5030_);
lean_dec_ref_known(v___x_5033_, 3);
v___x_5035_ = lean_string_utf8_extract(v_a_5003_, v___x_5031_, v___x_5034_);
lean_dec(v___x_5034_);
lean_dec(v_a_5003_);
v___x_5036_ = lean_string_utf8_byte_size(v___x_5035_);
lean_inc_ref(v___x_5035_);
v___x_5037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5037_, 0, v___x_5035_);
lean_ctor_set(v___x_5037_, 1, v___x_5031_);
lean_ctor_set(v___x_5037_, 2, v___x_5036_);
v___x_5038_ = l_String_Slice_Pos_prev_x3f(v___x_5037_, v___x_5036_);
if (lean_obj_tag(v___x_5038_) == 0)
{
uint32_t v___x_5039_; 
lean_dec_ref_known(v___x_5037_, 3);
v___x_5039_ = 65;
v___y_5012_ = v___x_5030_;
v___y_5013_ = v___x_5035_;
v___y_5014_ = v___x_5031_;
v___y_5015_ = v___x_5039_;
goto v___jp_5011_;
}
else
{
lean_object* v_val_5040_; lean_object* v___x_5041_; 
v_val_5040_ = lean_ctor_get(v___x_5038_, 0);
lean_inc(v_val_5040_);
lean_dec_ref_known(v___x_5038_, 1);
v___x_5041_ = l_String_Slice_Pos_get_x3f(v___x_5037_, v_val_5040_);
lean_dec(v_val_5040_);
lean_dec_ref_known(v___x_5037_, 3);
if (lean_obj_tag(v___x_5041_) == 0)
{
uint32_t v___x_5042_; 
v___x_5042_ = 65;
v___y_5012_ = v___x_5030_;
v___y_5013_ = v___x_5035_;
v___y_5014_ = v___x_5031_;
v___y_5015_ = v___x_5042_;
goto v___jp_5011_;
}
else
{
lean_object* v_val_5043_; uint32_t v___x_5044_; 
v_val_5043_ = lean_ctor_get(v___x_5041_, 0);
lean_inc(v_val_5043_);
lean_dec_ref_known(v___x_5041_, 1);
v___x_5044_ = lean_unbox_uint32(v_val_5043_);
lean_dec(v_val_5043_);
v___y_5012_ = v___x_5030_;
v___y_5013_ = v___x_5035_;
v___y_5014_ = v___x_5031_;
v___y_5015_ = v___x_5044_;
goto v___jp_5011_;
}
}
}
}
}
}
else
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5065_; 
lean_dec_ref(v_lines_4999_);
lean_dec_ref(v_s_4998_);
v_a_5058_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5065_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5065_ == 0)
{
v___x_5060_ = v___x_5002_;
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v___x_5002_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v___x_5063_; 
if (v_isShared_5061_ == 0)
{
v___x_5063_ = v___x_5060_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_a_5058_);
v___x_5063_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
return v___x_5063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_System_IO_0__IO_FS_Stream_lines_read___boxed(lean_object* v_s_5066_, lean_object* v_lines_5067_, lean_object* v_a_5068_){
_start:
{
lean_object* v_res_5069_; 
v_res_5069_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_5066_, v_lines_5067_);
return v_res_5069_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines(lean_object* v_s_5070_){
_start:
{
lean_object* v___x_5072_; lean_object* v___x_5073_; 
v___x_5072_ = ((lean_object*)(l_IO_FS_Handle_lines___closed__0));
v___x_5073_ = l___private_Init_System_IO_0__IO_FS_Stream_lines_read(v_s_5070_, v___x_5072_);
return v___x_5073_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_lines___boxed(lean_object* v_s_5074_, lean_object* v_a_5075_){
_start:
{
lean_object* v_res_5076_; 
v_res_5076_ = l_IO_FS_Stream_lines(v_s_5074_);
return v_res_5076_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0(lean_object* v_bOut_5077_){
_start:
{
lean_object* v___x_5079_; 
v___x_5079_ = lean_st_ref_get(v_bOut_5077_);
return v___x_5079_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed(lean_object* v_bOut_5080_, lean_object* v___y_5081_){
_start:
{
lean_object* v_res_5082_; 
v_res_5082_ = l_IO_FS_withIsolatedStreams___redArg___lam__0(v_bOut_5080_);
lean_dec(v_bOut_5080_);
return v_res_5082_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; 
v___x_5087_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__3));
v___x_5088_ = lean_unsigned_to_nat(46u);
v___x_5089_ = lean_unsigned_to_nat(193u);
v___x_5090_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__2));
v___x_5091_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__1));
v___x_5092_ = l_mkPanicMessageWithDecl(v___x_5091_, v___x_5090_, v___x_5089_, v___x_5088_, v___x_5087_);
return v___x_5092_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__1(lean_object* v_r_5093_, lean_object* v_toPure_5094_, lean_object* v_bOut_5095_){
_start:
{
lean_object* v___y_5097_; lean_object* v_data_5100_; uint8_t v___x_5101_; 
v_data_5100_ = lean_ctor_get(v_bOut_5095_, 0);
lean_inc_ref(v_data_5100_);
lean_dec_ref(v_bOut_5095_);
v___x_5101_ = lean_string_validate_utf8(v_data_5100_);
if (v___x_5101_ == 0)
{
lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
lean_dec_ref(v_data_5100_);
v___x_5102_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0));
v___x_5103_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4, &l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4_once, _init_l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__4);
v___x_5104_ = l_panic___redArg(v___x_5102_, v___x_5103_);
v___y_5097_ = v___x_5104_;
goto v___jp_5096_;
}
else
{
lean_object* v___x_5105_; 
v___x_5105_ = lean_string_from_utf8_unchecked(v_data_5100_);
v___y_5097_ = v___x_5105_;
goto v___jp_5096_;
}
v___jp_5096_:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; 
v___x_5098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5098_, 0, v___y_5097_);
lean_ctor_set(v___x_5098_, 1, v_r_5093_);
v___x_5099_ = lean_apply_2(v_toPure_5094_, lean_box(0), v___x_5098_);
return v___x_5099_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__2(lean_object* v_toPure_5106_, lean_object* v_inst_5107_, lean_object* v___f_5108_, lean_object* v_toBind_5109_, lean_object* v_r_5110_){
_start:
{
lean_object* v___f_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
v___f_5111_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5111_, 0, v_r_5110_);
lean_closure_set(v___f_5111_, 1, v_toPure_5106_);
v___x_5112_ = lean_apply_2(v_inst_5107_, lean_box(0), v___f_5108_);
v___x_5113_ = lean_apply_4(v_toBind_5109_, lean_box(0), lean_box(0), v___x_5112_, v___f_5111_);
return v___x_5113_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3(lean_object* v_toPure_5114_, lean_object* v_inst_5115_, lean_object* v_toBind_5116_, lean_object* v_bIn_5117_, lean_object* v_inst_5118_, lean_object* v_inst_5119_, uint8_t v_isolateStderr_5120_, lean_object* v_x_5121_, lean_object* v_bOut_5122_){
_start:
{
lean_object* v___f_5123_; lean_object* v___f_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___y_5128_; 
lean_inc(v_bOut_5122_);
v___f_5123_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5123_, 0, v_bOut_5122_);
lean_inc(v_toBind_5116_);
lean_inc(v_inst_5115_);
v___f_5124_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__2), 5, 4);
lean_closure_set(v___f_5124_, 0, v_toPure_5114_);
lean_closure_set(v___f_5124_, 1, v_inst_5115_);
lean_closure_set(v___f_5124_, 2, v___f_5123_);
lean_closure_set(v___f_5124_, 3, v_toBind_5116_);
v___x_5125_ = l_IO_FS_Stream_ofBuffer(v_bIn_5117_);
v___x_5126_ = l_IO_FS_Stream_ofBuffer(v_bOut_5122_);
if (v_isolateStderr_5120_ == 0)
{
v___y_5128_ = v_x_5121_;
goto v___jp_5127_;
}
else
{
lean_object* v___x_5132_; 
lean_inc_ref(v___x_5126_);
lean_inc(v_inst_5115_);
lean_inc(v_inst_5119_);
lean_inc_ref(v_inst_5118_);
v___x_5132_ = l_IO_withStderr___redArg(v_inst_5118_, v_inst_5119_, v_inst_5115_, v___x_5126_, v_x_5121_);
v___y_5128_ = v___x_5132_;
goto v___jp_5127_;
}
v___jp_5127_:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; 
lean_inc(v_inst_5115_);
lean_inc(v_inst_5119_);
lean_inc_ref(v_inst_5118_);
v___x_5129_ = l_IO_withStdout___redArg(v_inst_5118_, v_inst_5119_, v_inst_5115_, v___x_5126_, v___y_5128_);
v___x_5130_ = l_IO_withStdin___redArg(v_inst_5118_, v_inst_5119_, v_inst_5115_, v___x_5125_, v___x_5129_);
v___x_5131_ = lean_apply_4(v_toBind_5116_, lean_box(0), lean_box(0), v___x_5130_, v___f_5124_);
return v___x_5131_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed(lean_object* v_toPure_5133_, lean_object* v_inst_5134_, lean_object* v_toBind_5135_, lean_object* v_bIn_5136_, lean_object* v_inst_5137_, lean_object* v_inst_5138_, lean_object* v_isolateStderr_5139_, lean_object* v_x_5140_, lean_object* v_bOut_5141_){
_start:
{
uint8_t v_isolateStderr_boxed_5142_; lean_object* v_res_5143_; 
v_isolateStderr_boxed_5142_ = lean_unbox(v_isolateStderr_5139_);
v_res_5143_ = l_IO_FS_withIsolatedStreams___redArg___lam__3(v_toPure_5133_, v_inst_5134_, v_toBind_5135_, v_bIn_5136_, v_inst_5137_, v_inst_5138_, v_isolateStderr_boxed_5142_, v_x_5140_, v_bOut_5141_);
return v_res_5143_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4(lean_object* v_toPure_5144_, lean_object* v_inst_5145_, lean_object* v_toBind_5146_, lean_object* v_inst_5147_, lean_object* v_inst_5148_, uint8_t v_isolateStderr_5149_, lean_object* v_x_5150_, lean_object* v___x_5151_, lean_object* v_bIn_5152_){
_start:
{
lean_object* v___x_5153_; lean_object* v___f_5154_; lean_object* v___x_5155_; 
v___x_5153_ = lean_box(v_isolateStderr_5149_);
lean_inc(v_toBind_5146_);
v___f_5154_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_5154_, 0, v_toPure_5144_);
lean_closure_set(v___f_5154_, 1, v_inst_5145_);
lean_closure_set(v___f_5154_, 2, v_toBind_5146_);
lean_closure_set(v___f_5154_, 3, v_bIn_5152_);
lean_closure_set(v___f_5154_, 4, v_inst_5147_);
lean_closure_set(v___f_5154_, 5, v_inst_5148_);
lean_closure_set(v___f_5154_, 6, v___x_5153_);
lean_closure_set(v___f_5154_, 7, v_x_5150_);
v___x_5155_ = lean_apply_4(v_toBind_5146_, lean_box(0), lean_box(0), v___x_5151_, v___f_5154_);
return v___x_5155_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed(lean_object* v_toPure_5156_, lean_object* v_inst_5157_, lean_object* v_toBind_5158_, lean_object* v_inst_5159_, lean_object* v_inst_5160_, lean_object* v_isolateStderr_5161_, lean_object* v_x_5162_, lean_object* v___x_5163_, lean_object* v_bIn_5164_){
_start:
{
uint8_t v_isolateStderr_boxed_5165_; lean_object* v_res_5166_; 
v_isolateStderr_boxed_5165_ = lean_unbox(v_isolateStderr_5161_);
v_res_5166_ = l_IO_FS_withIsolatedStreams___redArg___lam__4(v_toPure_5156_, v_inst_5157_, v_toBind_5158_, v_inst_5159_, v_inst_5160_, v_isolateStderr_boxed_5165_, v_x_5162_, v___x_5163_, v_bIn_5164_);
return v_res_5166_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__0(void){
_start:
{
lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; 
v___x_5167_ = lean_unsigned_to_nat(0u);
v___x_5168_ = l_ByteArray_empty;
v___x_5169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5169_, 0, v___x_5168_);
lean_ctor_set(v___x_5169_, 1, v___x_5167_);
return v___x_5169_;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___redArg___closed__1(void){
_start:
{
lean_object* v___x_5170_; lean_object* v___x_5171_; 
v___x_5170_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___closed__0, &l_IO_FS_withIsolatedStreams___redArg___closed__0_once, _init_l_IO_FS_withIsolatedStreams___redArg___closed__0);
v___x_5171_ = lean_alloc_closure((void*)(l_IO_mkRef___boxed), 3, 2);
lean_closure_set(v___x_5171_, 0, lean_box(0));
lean_closure_set(v___x_5171_, 1, v___x_5170_);
return v___x_5171_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object* v_inst_5172_, lean_object* v_inst_5173_, lean_object* v_inst_5174_, lean_object* v_x_5175_, uint8_t v_isolateStderr_5176_){
_start:
{
lean_object* v_toApplicative_5177_; lean_object* v_toBind_5178_; lean_object* v_toPure_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___f_5183_; lean_object* v___x_5184_; 
v_toApplicative_5177_ = lean_ctor_get(v_inst_5172_, 0);
v_toBind_5178_ = lean_ctor_get(v_inst_5172_, 1);
lean_inc_n(v_toBind_5178_, 2);
v_toPure_5179_ = lean_ctor_get(v_toApplicative_5177_, 1);
lean_inc(v_toPure_5179_);
v___x_5180_ = lean_obj_once(&l_IO_FS_withIsolatedStreams___redArg___closed__1, &l_IO_FS_withIsolatedStreams___redArg___closed__1_once, _init_l_IO_FS_withIsolatedStreams___redArg___closed__1);
lean_inc(v_inst_5174_);
v___x_5181_ = lean_apply_2(v_inst_5174_, lean_box(0), v___x_5180_);
v___x_5182_ = lean_box(v_isolateStderr_5176_);
lean_inc(v___x_5181_);
v___f_5183_ = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_5183_, 0, v_toPure_5179_);
lean_closure_set(v___f_5183_, 1, v_inst_5174_);
lean_closure_set(v___f_5183_, 2, v_toBind_5178_);
lean_closure_set(v___f_5183_, 3, v_inst_5172_);
lean_closure_set(v___f_5183_, 4, v_inst_5173_);
lean_closure_set(v___f_5183_, 5, v___x_5182_);
lean_closure_set(v___f_5183_, 6, v_x_5175_);
lean_closure_set(v___f_5183_, 7, v___x_5181_);
v___x_5184_ = lean_apply_4(v_toBind_5178_, lean_box(0), lean_box(0), v___x_5181_, v___f_5183_);
return v___x_5184_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___redArg___boxed(lean_object* v_inst_5185_, lean_object* v_inst_5186_, lean_object* v_inst_5187_, lean_object* v_x_5188_, lean_object* v_isolateStderr_5189_){
_start:
{
uint8_t v_isolateStderr_boxed_5190_; lean_object* v_res_5191_; 
v_isolateStderr_boxed_5190_ = lean_unbox(v_isolateStderr_5189_);
v_res_5191_ = l_IO_FS_withIsolatedStreams___redArg(v_inst_5185_, v_inst_5186_, v_inst_5187_, v_x_5188_, v_isolateStderr_boxed_5190_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams(lean_object* v_m_5192_, lean_object* v_00_u03b1_5193_, lean_object* v_inst_5194_, lean_object* v_inst_5195_, lean_object* v_inst_5196_, lean_object* v_x_5197_, uint8_t v_isolateStderr_5198_){
_start:
{
lean_object* v___x_5199_; 
v___x_5199_ = l_IO_FS_withIsolatedStreams___redArg(v_inst_5194_, v_inst_5195_, v_inst_5196_, v_x_5197_, v_isolateStderr_5198_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___boxed(lean_object* v_m_5200_, lean_object* v_00_u03b1_5201_, lean_object* v_inst_5202_, lean_object* v_inst_5203_, lean_object* v_inst_5204_, lean_object* v_x_5205_, lean_object* v_isolateStderr_5206_){
_start:
{
uint8_t v_isolateStderr_boxed_5207_; lean_object* v_res_5208_; 
v_isolateStderr_boxed_5207_ = lean_unbox(v_isolateStderr_5206_);
v_res_5208_ = l_IO_FS_withIsolatedStreams(v_m_5200_, v_00_u03b1_5201_, v_inst_5202_, v_inst_5203_, v_inst_5204_, v_x_5205_, v_isolateStderr_boxed_5207_);
return v_res_5208_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9(void){
_start:
{
lean_object* v___x_5265_; lean_object* v___x_5266_; 
v___x_5265_ = ((lean_object*)(l_IO_FS_withIsolatedStreams___redArg___lam__1___closed__0));
v___x_5266_ = l_String_toRawSubstring_x27(v___x_5265_);
return v___x_5266_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17(void){
_start:
{
lean_object* v___x_5281_; lean_object* v___x_5282_; 
v___x_5281_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__16));
v___x_5282_ = l_String_toRawSubstring_x27(v___x_5281_);
return v___x_5282_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24(void){
_start:
{
lean_object* v___x_5295_; lean_object* v___x_5296_; 
v___x_5295_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__18));
v___x_5296_ = l_String_toRawSubstring_x27(v___x_5295_);
return v___x_5296_;
}
}
static lean_object* _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31(void){
_start:
{
lean_object* v___x_5311_; lean_object* v___x_5312_; 
v___x_5311_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__30));
v___x_5312_ = l_String_toRawSubstring_x27(v___x_5311_);
return v___x_5312_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1(lean_object* v_x_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_){
_start:
{
lean_object* v___x_5340_; uint8_t v___x_5341_; 
v___x_5340_ = ((lean_object*)(l_termPrintln_x21_____00__closed__1));
lean_inc(v_x_5337_);
v___x_5341_ = l_Lean_Syntax_isOfKind(v_x_5337_, v___x_5340_);
if (v___x_5341_ == 0)
{
lean_object* v___x_5342_; lean_object* v___x_5343_; 
lean_dec(v_x_5337_);
v___x_5342_ = lean_box(1);
v___x_5343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5343_, 0, v___x_5342_);
lean_ctor_set(v___x_5343_, 1, v_a_5339_);
return v___x_5343_;
}
else
{
lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; uint8_t v___x_5347_; 
v___x_5344_ = lean_unsigned_to_nat(1u);
v___x_5345_ = l_Lean_Syntax_getArg(v_x_5337_, v___x_5344_);
lean_dec(v_x_5337_);
v___x_5346_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__1));
lean_inc(v___x_5345_);
v___x_5347_ = l_Lean_Syntax_isOfKind(v___x_5345_, v___x_5346_);
if (v___x_5347_ == 0)
{
lean_object* v_quotContext_5348_; lean_object* v_currMacroScope_5349_; lean_object* v_ref_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; 
v_quotContext_5348_ = lean_ctor_get(v_a_5338_, 1);
v_currMacroScope_5349_ = lean_ctor_get(v_a_5338_, 2);
v_ref_5350_ = lean_ctor_get(v_a_5338_, 5);
v___x_5351_ = l_Lean_SourceInfo_fromRef(v_ref_5350_, v___x_5347_);
v___x_5352_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3));
v___x_5353_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5));
v___x_5354_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6));
lean_inc_n(v___x_5351_, 14);
v___x_5355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5355_, 0, v___x_5351_);
lean_ctor_set(v___x_5355_, 1, v___x_5354_);
v___x_5356_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8));
v___x_5357_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
v___x_5358_ = lean_box(0);
lean_inc_n(v_currMacroScope_5349_, 4);
lean_inc_n(v_quotContext_5348_, 4);
v___x_5359_ = l_Lean_addMacroScope(v_quotContext_5348_, v___x_5358_, v_currMacroScope_5349_);
v___x_5360_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15));
v___x_5361_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5361_, 0, v___x_5351_);
lean_ctor_set(v___x_5361_, 1, v___x_5357_);
lean_ctor_set(v___x_5361_, 2, v___x_5359_);
lean_ctor_set(v___x_5361_, 3, v___x_5360_);
v___x_5362_ = l_Lean_Syntax_node1(v___x_5351_, v___x_5356_, v___x_5361_);
v___x_5363_ = l_Lean_Syntax_node2(v___x_5351_, v___x_5353_, v___x_5355_, v___x_5362_);
v___x_5364_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_5365_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
v___x_5366_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20));
v___x_5367_ = l_Lean_addMacroScope(v_quotContext_5348_, v___x_5366_, v_currMacroScope_5349_);
v___x_5368_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22));
v___x_5369_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5369_, 0, v___x_5351_);
lean_ctor_set(v___x_5369_, 1, v___x_5365_);
lean_ctor_set(v___x_5369_, 2, v___x_5367_);
lean_ctor_set(v___x_5369_, 3, v___x_5368_);
v___x_5370_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_5371_ = l_Lean_Syntax_node1(v___x_5351_, v___x_5370_, v___x_5345_);
v___x_5372_ = l_Lean_Syntax_node2(v___x_5351_, v___x_5364_, v___x_5369_, v___x_5371_);
v___x_5373_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23));
v___x_5374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5374_, 0, v___x_5351_);
lean_ctor_set(v___x_5374_, 1, v___x_5373_);
v___x_5375_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
v___x_5376_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25));
v___x_5377_ = l_Lean_addMacroScope(v_quotContext_5348_, v___x_5376_, v_currMacroScope_5349_);
v___x_5378_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29));
v___x_5379_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5379_, 0, v___x_5351_);
lean_ctor_set(v___x_5379_, 1, v___x_5375_);
lean_ctor_set(v___x_5379_, 2, v___x_5377_);
lean_ctor_set(v___x_5379_, 3, v___x_5378_);
v___x_5380_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
v___x_5381_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32));
v___x_5382_ = l_Lean_addMacroScope(v_quotContext_5348_, v___x_5381_, v_currMacroScope_5349_);
v___x_5383_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36));
v___x_5384_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5384_, 0, v___x_5351_);
lean_ctor_set(v___x_5384_, 1, v___x_5380_);
lean_ctor_set(v___x_5384_, 2, v___x_5382_);
lean_ctor_set(v___x_5384_, 3, v___x_5383_);
v___x_5385_ = l_Lean_Syntax_node1(v___x_5351_, v___x_5370_, v___x_5384_);
v___x_5386_ = l_Lean_Syntax_node2(v___x_5351_, v___x_5364_, v___x_5379_, v___x_5385_);
v___x_5387_ = l_Lean_Syntax_node1(v___x_5351_, v___x_5370_, v___x_5386_);
v___x_5388_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37));
v___x_5389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5389_, 0, v___x_5351_);
lean_ctor_set(v___x_5389_, 1, v___x_5388_);
v___x_5390_ = l_Lean_Syntax_node5(v___x_5351_, v___x_5352_, v___x_5363_, v___x_5372_, v___x_5374_, v___x_5387_, v___x_5389_);
v___x_5391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5391_, 0, v___x_5390_);
lean_ctor_set(v___x_5391_, 1, v_a_5339_);
return v___x_5391_;
}
else
{
lean_object* v_quotContext_5392_; lean_object* v_currMacroScope_5393_; lean_object* v_ref_5394_; uint8_t v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; 
v_quotContext_5392_ = lean_ctor_get(v_a_5338_, 1);
v_currMacroScope_5393_ = lean_ctor_get(v_a_5338_, 2);
v_ref_5394_ = lean_ctor_get(v_a_5338_, 5);
v___x_5395_ = 0;
v___x_5396_ = l_Lean_SourceInfo_fromRef(v_ref_5394_, v___x_5395_);
v___x_5397_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__3));
v___x_5398_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__5));
v___x_5399_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__6));
lean_inc_n(v___x_5396_, 17);
v___x_5400_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5400_, 0, v___x_5396_);
lean_ctor_set(v___x_5400_, 1, v___x_5399_);
v___x_5401_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__8));
v___x_5402_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__9);
v___x_5403_ = lean_box(0);
lean_inc_n(v_currMacroScope_5393_, 4);
lean_inc_n(v_quotContext_5392_, 4);
v___x_5404_ = l_Lean_addMacroScope(v_quotContext_5392_, v___x_5403_, v_currMacroScope_5393_);
v___x_5405_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__15));
v___x_5406_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5406_, 0, v___x_5396_);
lean_ctor_set(v___x_5406_, 1, v___x_5402_);
lean_ctor_set(v___x_5406_, 2, v___x_5404_);
lean_ctor_set(v___x_5406_, 3, v___x_5405_);
v___x_5407_ = l_Lean_Syntax_node1(v___x_5396_, v___x_5401_, v___x_5406_);
v___x_5408_ = l_Lean_Syntax_node2(v___x_5396_, v___x_5398_, v___x_5400_, v___x_5407_);
v___x_5409_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__16));
v___x_5410_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__17);
v___x_5411_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__20));
v___x_5412_ = l_Lean_addMacroScope(v_quotContext_5392_, v___x_5411_, v_currMacroScope_5393_);
v___x_5413_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__22));
v___x_5414_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5414_, 0, v___x_5396_);
lean_ctor_set(v___x_5414_, 1, v___x_5410_);
lean_ctor_set(v___x_5414_, 2, v___x_5412_);
lean_ctor_set(v___x_5414_, 3, v___x_5413_);
v___x_5415_ = ((lean_object*)(l_IO_waitAny___auto__1___closed__9));
v___x_5416_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__39));
v___x_5417_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__41));
v___x_5418_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__42));
v___x_5419_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5419_, 0, v___x_5396_);
lean_ctor_set(v___x_5419_, 1, v___x_5418_);
v___x_5420_ = l_Lean_Syntax_node2(v___x_5396_, v___x_5417_, v___x_5419_, v___x_5345_);
v___x_5421_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__37));
v___x_5422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5422_, 0, v___x_5396_);
lean_ctor_set(v___x_5422_, 1, v___x_5421_);
lean_inc_ref(v___x_5422_);
lean_inc(v___x_5408_);
v___x_5423_ = l_Lean_Syntax_node3(v___x_5396_, v___x_5416_, v___x_5408_, v___x_5420_, v___x_5422_);
v___x_5424_ = l_Lean_Syntax_node1(v___x_5396_, v___x_5415_, v___x_5423_);
v___x_5425_ = l_Lean_Syntax_node2(v___x_5396_, v___x_5409_, v___x_5414_, v___x_5424_);
v___x_5426_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__23));
v___x_5427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5427_, 0, v___x_5396_);
lean_ctor_set(v___x_5427_, 1, v___x_5426_);
v___x_5428_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__24);
v___x_5429_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__25));
v___x_5430_ = l_Lean_addMacroScope(v_quotContext_5392_, v___x_5429_, v_currMacroScope_5393_);
v___x_5431_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__29));
v___x_5432_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5432_, 0, v___x_5396_);
lean_ctor_set(v___x_5432_, 1, v___x_5428_);
lean_ctor_set(v___x_5432_, 2, v___x_5430_);
lean_ctor_set(v___x_5432_, 3, v___x_5431_);
v___x_5433_ = lean_obj_once(&l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31, &l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31_once, _init_l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__31);
v___x_5434_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__32));
v___x_5435_ = l_Lean_addMacroScope(v_quotContext_5392_, v___x_5434_, v_currMacroScope_5393_);
v___x_5436_ = ((lean_object*)(l___aux__Init__System__IO______macroRules__termPrintln_x21______1___closed__36));
v___x_5437_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5437_, 0, v___x_5396_);
lean_ctor_set(v___x_5437_, 1, v___x_5433_);
lean_ctor_set(v___x_5437_, 2, v___x_5435_);
lean_ctor_set(v___x_5437_, 3, v___x_5436_);
v___x_5438_ = l_Lean_Syntax_node1(v___x_5396_, v___x_5415_, v___x_5437_);
v___x_5439_ = l_Lean_Syntax_node2(v___x_5396_, v___x_5409_, v___x_5432_, v___x_5438_);
v___x_5440_ = l_Lean_Syntax_node1(v___x_5396_, v___x_5415_, v___x_5439_);
v___x_5441_ = l_Lean_Syntax_node5(v___x_5396_, v___x_5397_, v___x_5408_, v___x_5425_, v___x_5427_, v___x_5440_, v___x_5422_);
v___x_5442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5442_, 0, v___x_5441_);
lean_ctor_set(v___x_5442_, 1, v_a_5339_);
return v___x_5442_;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__System__IO______macroRules__termPrintln_x21______1___boxed(lean_object* v_x_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_){
_start:
{
lean_object* v_res_5446_; 
v_res_5446_ = l___aux__Init__System__IO______macroRules__termPrintln_x21______1(v_x_5443_, v_a_5444_, v_a_5445_);
lean_dec_ref(v_a_5444_);
return v_res_5446_;
}
}
LEAN_EXPORT lean_object* l_Runtime_markMultiThreaded___boxed(lean_object* v_00_u03b1_5450_, lean_object* v_a_5451_, lean_object* v_a_00___x40___internal___hyg_5452_){
_start:
{
lean_object* v_res_5453_; 
v_res_5453_ = lean_runtime_mark_multi_threaded(v_a_5451_);
return v_res_5453_;
}
}
LEAN_EXPORT lean_object* l_Runtime_markPersistent___boxed(lean_object* v_00_u03b1_5457_, lean_object* v_a_5458_, lean_object* v_a_00___x40___internal___hyg_5459_){
_start:
{
lean_object* v_res_5460_; 
v_res_5460_ = lean_runtime_mark_persistent(v_a_5458_);
return v_res_5460_;
}
}
LEAN_EXPORT lean_object* l_Runtime_forget___boxed(lean_object* v_00_u03b1_5464_, lean_object* v_a_5465_, lean_object* v_a_00___x40___internal___hyg_5466_){
_start:
{
lean_object* v_res_5467_; 
v_res_5467_ = lean_runtime_forget(v_a_5465_);
return v_res_5467_;
}
}
LEAN_EXPORT lean_object* l_Runtime_hold___boxed(lean_object* v_00_u03b1_5471_, lean_object* v_a_5472_, lean_object* v_a_00___x40___internal___hyg_5473_){
_start:
{
lean_object* v_res_5474_; 
v_res_5474_ = lean_runtime_hold(v_a_5472_);
lean_dec(v_a_5472_);
return v_res_5474_;
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
